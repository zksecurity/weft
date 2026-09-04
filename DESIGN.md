# Verifying MPC circuits in Lean 4 — design notes

Working name: **Glean** (see §10 for alternatives). The reasons behind
each choice, with the alternatives rejected, are in `decisions/`, one
record per decision; this document describes the design as it stands.
Companion files:
`Glean.lean` (the core, type-checks; compositional lemmas are `sorry`,
everything else is real), `Gallery.lean` (ten circuits in different
styles, with their theorems closed by evaluation), `Features.lean` (the
MPC as a price list: feature sets in the type, subtyping, derived costs),
`FieldCirc.lean` (circuits needing a field), `MultiField.lean` (generic over
field types, switching, edaBits), `Timing.lean` (delay by dependency
tracking), `Gadget.lean` (circuits with assumptions and specs) and
`Privacy.lean` (simulation-based privacy on Mathlib's `PMF`: fresh coins are
jointly uniform, realisations on tagged views), `Compose.lean` (the
composition theorem, proved) and
`Functionality.lean` (functionalities and realisations as one notion) and
`AesHybrid.lean` (from the AES-hybrid to a plain circuit, end to end) and
`Cost.lean` (delay and communication as separate observables; the
composition theorems for cost) and `Beaver.lean` (multiplication from
triples: why the masks must be jointly uniform, with a counterexample).
The sketch depends on Mathlib.

## 1. What we are verifying, and what we are not

An *MPC circuit* here is a program that drives an ideal functionality
(an "arithmetic black box"): it hands the functionality shared values,
asks it to multiply, open, compare, and so on, and does ordinary
computation on whatever comes back in the clear.

We deliberately do **not** model the MPC protocol: no shares, no parties'
views, no network. The functionality is a black box whose behaviour is a
Lean definition. Three consequences shape everything below:

* **No witness, no soundness/completeness split.** A ZK circuit is a
  relation checked against a prover-supplied witness; an MPC circuit is a
  function of its inputs and of the coins the functionality hands out
  (`rand`, Beaver triples). The properties of interest are *functional
  correctness*, *cost* and *hiding*.
* **Interaction is the program.** Opening a value, computing on it in the
  clear and inserting the result back is not a special case; it is the
  basic shape of a circuit. So the circuit language is a monad whose
  effects are calls to the functionality, and the "reactive functionality"
  is just the interpreter of that monad.
* **Hiding is a property of the circuit, not of the protocol.** Because the
  functionality is ideal, the adversary's entire view is the list of values
  the circuit chose to open. "Reveals nothing beyond the output" becomes:
  *the distribution of that list is a function of the output*. For
  coin-free circuits the distribution is a point, the simulator is a
  plain function, and the statement is checked by evaluation; with coins
  it is an equation between distributions, proved by unfolding the run
  and one lemma: a uniform mask pushed through a bijection is uniform.

### Cues from Clean, and what does not carry over

Clean (the Lean 4 ZK framework) gets several things right that we copy:

| Clean                                             | Here                                                              |
|---------------------------------------------------|-------------------------------------------------------------------|
| Circuit is a monadic DSL; the monad records ops   | Same: `Circ σ` is a free monad over the functionality's signature |
| `ProvableType` maps structured Lean types to vars | `Domain` with abstract share type; structured `SharedType` (§3.3) |
| `FormalCircuit` bundles circuit + assumptions + spec + proofs | `Gadget` bundles circuit + spec + leakage bound + round bound (§6) |
| Subcircuits with local proofs compose             | Handlers compose circuits; cost/leak lemmas are compositional (§5) |

What does not apply: witness generation, constraints and their soundness,
lookups and table layout, the completeness/soundness pair, `Environment`
as an assignment of witness cells. There is no "elaborated circuit" as a
constraint system; the circuit *is* its own semantics.

## 2. Core model

### 2.1 Signatures: what the functionality offers

A signature is a family of request types indexed by the response type.
Encoding the response type as an index (rather than a `Ret : Op → Type`
function) means sums of signatures need no casts.

```lean
abbrev Sig : Type 1 := Type → Type          -- σ α = requests answered by an α

inductive Sig.Sum (σ τ : Sig) (α : Type) : Type where
  | inl : σ α → Sig.Sum σ τ α
  | inr : τ α → Sig.Sum σ τ α
infixr:35 " ⊞ " => Sig.Sum

class Has (τ σ : Sig) where                 -- feature set τ is available in σ
  inj : {α : Type} → τ α → σ α
```

Feature sets are small inductive families, each one an MPC *capability*:

```lean
structure Domain where (F : Type) (S : Type)   -- clear values / opaque shares

inductive Lin  (D : Domain) : Sig where       -- always free
  | const : D.F → Lin D D.S
  | add   : D.S → D.S → Lin D D.S
  | sub   : D.S → D.S → Lin D D.S
  | smul  : D.F → D.S → Lin D D.S
inductive Mult (D : Domain) : Sig where | mult  : D.S → D.S → Mult D D.S
inductive Reveal (D : Domain) : Sig where | reveal : D.S → Reveal D D.F
inductive Cmp  (D : Domain) : Sig where | lt    : D.S → D.S → Cmp D D.S
inductive Rand    (D : Domain) : Sig where | rand : Rand D D.S             -- fresh random share
inductive PubCoin (D : Domain) : Sig where | coin : PubCoin D D.F          -- public random value
inductive Get (D : Domain) (T : Domain → Type) : Sig where                 -- preprocessing box
  | get : MulTriple D (D.S × D.S × D.S)                                    -- (a, b, a·b), named after its promise

abbrev Std (D : Domain) : Sig := Lin D ⊞ Mult D ⊞ Reveal D          -- arithmetic black box
abbrev Pre (D : Domain) : Sig := Lin D ⊞ Reveal D ⊞ MulTriple D     -- preprocessing model
```

Randomness is a *feature of the functionality*, not of the circuit
language: `rand` and `mulTriple` are requests like any other. Which of them an
MPC offers, and what they cost, is again a signature and a cost model.

A circuit that only needs linear ops and multiplication is written against
`[Has (Lin D) σ] [Has (Mult D) σ]` and runs on *every* functionality whose
signature contains those. This is the "different subsets of features"
requirement, solved by the usual data-types-à-la-carte instances
(`Has.refl`, `Has.left`, `Has.right`).

### 2.2 Circuits: the free monad, plus parallelism

```lean
inductive Circ (σ : Sig) : Type → Type 1 where
  | pure : α → Circ σ α
  | call : σ β → (β → Circ σ α) → Circ σ α                     -- ask, then continue
  | par  : Circ σ β → Circ σ γ → (β × γ → Circ σ α) → Circ σ α  -- independent branches
```

`call o k` sends request `o` and continues with `k` on the response.
The continuation is arbitrary Lean code: that is where the "compute in the
clear and insert back" happens, with no special support.

```lean
def divByOpened [Has (Lin D) σ] [Has (Reveal D) σ] [Div D.F] [OfNat D.F 1]
    (x d : D.S) : Circ σ D.S := do
  let dv ← reveal d           -- functionality → environment
  smul (1 / dv) x            -- clear arithmetic, then environment → functionality
```

There is no parallel node. Monadic `bind` is sequential *as a program*, but
delay is not read off the program order: it is computed from data
dependencies in the timed domain (§3.5), so `mapM mul` over a list is one
round and a product tree written with plain binds costs its depth. The
only annotation a circuit ever needs is a `barrier` where it branches on a
revealed value (decision 002).

`Circ σ` is a lawful monad (`bind_pure`, `bind_assoc` by induction), so
`do`-notation, `List.mapM`, etc. all work, and the interpreter and every
compositional theorem have exactly two cases.

### 2.3 Why circuits cannot cheat

Circuits are polymorphic in the domain `D`. Since `D.S` is an abstract
type, the only functions from `D.S` to anything are the ones the signature
offers. A circuit cannot look at a share; it can only ask the functionality
to open it, and opening is exactly what the leakage semantics records.
(This is enforced by typing, not by a parametricity theorem: the hiding
theorems are about the circuit instantiated at the ideal domain and are
proved by evaluation.)

### 2.4 What a circuit looks like

A user writes against the features they need and nothing else. Here is the
whole of a one-round "dot product plus constant" and of Horner evaluation:

```lean
/-- ⟨xs, ys⟩ + c.  One round: the products in parallel, then free linear ops. -/
def dotPlus [Has (Lin D) σ] [Has (Mult D) σ] [OfNat D.F 0]
    (xs ys : List D.S) (c : D.F) : Circ σ D.S := do
  let ps ← Circ.parMap (fun p : D.S × D.S => mul p.1 p.2) (xs.zip ys)
  let s ← sumAll ps
  let k ← const c
  add s k

/-- Σ aᵢ xⁱ by Horner: each multiplication depends on the last, so n rounds. -/
def horner [Has (Lin D) σ] [Has (Mult D) σ] [OfNat D.F 0]
    (x : D.S) : List D.S → Circ σ D.S
  | [] => const (0 : D.F)
  | a :: as => do
    let r ← horner x as
    let t ← mul r x
    add t a
```

Things to notice:

* `D.S` is opaque, so `mul`, `add`, `const` are the only things that can
  happen to a share; `c : D.F` is a clear value the environment supplies.
* Parallelism is where you wrote it: `parMap` gives one round, the
  recursion in `horner` gives `n`. The framework does not reschedule.
* Nothing says which MPC this runs on. Instantiating `σ := Std D` runs it
  on the arithmetic black box; `σ := Pre D` (after the Beaver handler,
  §5) runs it on a preprocessing functionality; the theorems below are
  stated once and hold for both.

And what the user proves, all by `rfl` in the sketch for concrete sizes:

```lean
example : output (Std.ideal F) (dotPlus [a, b] [c, c] k) = a * c + b * c + k := rfl
example : delay F (Std.timed F) (dotPlus [⟪a⟫, ⟪b⟫] [⟪a⟫, ⟪b⟫] k) = 1 := rfl   -- timed domain, §3.5
example : delay F (Std.timed F) (horner ⟪x⟫ [⟪a₀⟫, ⟪a₁⟫, ⟪a₂⟫]) = 3 := rfl
example : leak (Std.ideal F) (horner x [a₀, a₁, a₂]) = [] := rfl     -- hence hiding
```

### 2.5 Polymorphism over the feature set

`[Has τ σ]` makes a circuit *run* on every functionality that has `τ`. A
circuit whose *implementation* should depend on what is available (an AES
S-box that uses native inversion when the MPC offers it and `x^254`
otherwise) is written against a **capability class**, whose instances are
the strategies:

```lean
inductive Inv (D : Domain) : Sig where | inv : D.S → Inv D D.S      -- native feature

class HasInv (D : Domain) (σ : Sig) where                              -- "some way to invert"
  inv : D.S → Circ σ D.S

instance (priority := high) [Has (Inv D) σ] : HasInv D σ := ⟨fun x => Circ.op (Inv.inv x)⟩
instance [Has (Lin D) σ] [Has (Mult D) σ] [OfNat D.F 1] : HasInv D σ := ⟨fun x => expPublic x 254⟩

def sbox [HasInv D σ] [Has (Lin D) σ] (affine : D.S → Circ σ D.S) (x : D.S) : Circ σ D.S := do
  let y ← HasInv.inv x
  affine y
```

Instance priority picks the native feature when the signature has it and
falls back otherwise. The S-box source is written once; on `Std` it costs
13 rounds, on `Std ⊞ Inv` one round, both by evaluation. Correctness is
proved per instance against the same spec (`output = x⁻¹` then affine), so
a capability class carries a *spec* the way a `Gadget` does (§7): every
strategy must meet it, and a caller's proof uses only the spec. This is the
MPC analogue of Clean's subcircuits with local proofs, with the extra twist
that which subcircuit you get is decided by the type class.

The same mechanism, one level up, handles whole functionalities: an AES
*functionality* offered natively by some MPC (`Aes D : Sig`, one round,
opaque) versus an AES *circuit* over `Std`. Both are instances of
`HasAes D σ`; a protocol written against `HasAes` runs on either.

### 2.6 The MPC as one value: a price list

Should the set of enabled features be part of the circuit's type, with
subtyping to require a feature? Yes, and there should be exactly one thing
that describes an MPC. The design that satisfies both, worked out in
`Features.lean`:

**An MPC is what it charges.** It is a list of `(feature, price)` pairs.
A feature that is absent is not offered, which is the same as infinitely
expensive. Everything else is derived from that one value:

```lean
inductive Feature where | lin | mult | reveal | rand | randNZ | mulTriple | cmp | inv     -- library-owned
def Feature.Ops (D : Domain) : Feature → Sig                                 -- lin ↦ Lin D, …

structure MPC where prices : List (Feature × Nat)

def MPC.cost (M : MPC) (f : Feature) : Option Nat := (M.prices.find? (·.1 = f)).map (·.2)

class Has (f : Feature) (M : MPC) : Prop where mem : ∃ n, (f, n) ∈ M.prices  -- by instance search
theorem Has.finite [Has f M] : M.cost f ≠ none

def Ops (D : Domain) (M : MPC) : Sig := fun α => Σ f : { f // Has f M }, f.1.Ops D α
abbrev Circ' (D : Domain) (M : MPC) (α : Type) := Circ (Ops D M) α
```

* **The type carries the feature set.** `Circ' D M α` may only use what
  `M` offers: a request is a feature *with its `Has` evidence* and one of
  that feature's operations. Calling `inv` against an MPC without it is
  a failed instance search at the call site, not a runtime `⊤`.
* **`Has` implies finite cost, by construction.** The cost model of `M` is
  derived (`M.delay` prices each request by its feature), every request
  in a well-typed circuit carries `Has`, and `Has.finite` gives the price.
  So `cost M.delay c ≠ none` for every circuit that type-checks
  (`cost_finite`, statement in the sketch), and `⊤` is only ever the
  price of something the type system already ruled out.
* **Subtyping is `M.le M' := ∀ f, Has f M → Has f M'`**, and `widen h`
  coerces `Circ' D M α` to `Circ' D M' α`. It is a handler, so it costs
  nothing and changes nothing semantically.
* **Semantics is per feature, once.** `Feature.ideal f` is the ideal model
  of feature `f`; `M.ideal` assembles it for any `M`. An MPC only prices,
  it never redefines what an operation means. Two MPCs that both offer
  `mult` agree on what `mult` computes and leaks, and differ only in
  rounds.

The capability-class pattern of §2.5 is unchanged: instances of
`HasInv D σ` become `instance [Has .inv M] : HasInv D M` (native) and
`instance [Has .lin M] [Has .mult M] : HasInv D M` (fallback), and the
choice can also be made by comparing `M.cost .inv` with the fallback's
known price, since that is now a plain `Option Nat` on a plain value.

This also removes the wrinkle from before: prices are per *feature*, not
per request, so nothing needs an argument to be priced.

**Cost of the closed world.** `Feature` is an enumeration owned by the
library, so a downstream user cannot add a feature without editing it.
That is the trade for feature sets being first-class, decidable and
printable. If open extension matters, `Feature` can be a structure with a
name and its signature and `Has` can be by name, at the price of giving
up exhaustiveness checks. For a library that ships the features, the
closed world is the right default.

### 2.7 Adding features later must not break anything

The user-visible contract is: a circuit that did not use a feature is
unaffected by that feature being added, to the library or to an MPC.
Three disciplines guarantee it, and `Features.lean` tests all three:

1. **Circuits state lower bounds, never a set.** A circuit is
   `{M : MPC} [Has .lin M] [Has .mult M] … : Circ' D M α`. It is generic
   in `M`; only examples and top-level deployments pin `M`. A larger `M`
   still satisfies the bounds.
2. **MPCs are lists, and absence is the default.** Adding a feature to the
   library adds a constructor; `MPC.cost` already returns `none` for it
   on every existing MPC. Adding a feature to an MPC appends to its list;
   every `Has` that held before still holds (`widen` with the
   `mem_cons_of_mem` witness is the coercion, and it is one line).
3. **Per-feature semantics, total functions with wildcards elsewhere.**
   `Feature.Ops` and `Feature.ideal` are library-owned total functions,
   so the compiler names the two places that need a case. User-written
   cost functions or models over `Feature` end in `| _ => none`.

What survives unchanged: every circuit, every theorem about it stated with
price hypotheses (§4.2) or against a named MPC value, and every
`Gadget` (§7), whose `requires` is exactly its list of `Has` bounds.

### 2.8 Circuits over a field

The algebra of the clear type is a property of the domain, `D.F`, not a
feature of the MPC. A circuit that needs it says so with a class
constraint next to its `Has` bounds; with Mathlib that is `Field D.F` (the
sketch uses a stand-in with the same operations):

```lean
/-- Lagrange interpolation at a public point: coefficients need division,
computed in the clear; the combination is linear.  Zero rounds. -/
def interpolate {D : Domain} [Field D.F] [DecidableEq D.F] {M : MPC} [Has .lin M]
    (nodes : List D.F) (ys : List D.S) (x : D.F) : Circ' D M D.S := do
  let coeff (xi : D.F) : D.F :=
    (nodes.filter (· ≠ xi)).foldl (fun acc xj => acc * ((x - xj) / (xi - xj))) 1
  let terms ← Circ.parMap (fun p : D.F × D.S => smul (coeff p.1) p.2) (nodes.zip ys)
  sumAll terms

/-- Inversion by masking: `1/x = s / open(x·s)`.  Division in the clear, and coins. -/
def invert {D : Domain} [Field D.F] {M : MPC} [Has .lin M] [Has .mult M] [Has .rand M] [Has .reveal M]
    (x : D.S) : Circ' D M D.S := do
  let s ← rand
  let v ← mul x s
  let m ← reveal v
  smul (1 / m) s
```

Three things follow. A ring-only MPC (`ℤ/2^k`) has a domain whose `D.F`
does not satisfy `Field`, so `invert` does not elaborate against it, while
a circuit asking only for `CommRing D.F` runs on both. Correctness proofs
of field circuits are field algebra (`field_simp`, `ring`) on the
output, for every value of the mask, e.g. `(x·s)⁻¹·s = x⁻¹` for `invert`
with `s ≠ 0`. The mask comes from `randNZ`, a random *nonzero* share the
functionality guarantees, so `invert` is perfectly correct and perfectly
hiding: the opened `x·s` is a uniform nonzero element (`invert_correct`,
`invertGadget`). With a plain `rand` the same circuit would be correct
and hiding only off `s = 0`; that is where statistical error (§8) would
enter, and the design keeps it out by asking the functionality for what
the proof needs.

### 2.9 Several fields: generic over the field, switching as a capability

Fields are not named or numbered. Shares are a type constructor, `D.S F`
is "a share of an `F`", every operation is generic over `F`, the field's
algebra is a typeclass on `F`, and switching is a capability over two
field *types* (`MultiField.lean`):

```lean
structure Domain where S : Type → Type                  -- the circuit's opaque view of shares
abbrev Domain.at (D : Domain) (F : Type) : Glean.Domain := ⟨F, D.S F⟩   -- reuse every single-field feature

inductive Switch (D : Domain) (F G : Type) : Sig where
  | switch : D.S F → Switch D F G (D.S G)

/-- What an MPC offers: a feature on a field, or switching between two.
The field's instances travel with the entry. -/
inductive Cap where
  | on (f : Feature) (F : Type) [Concrete F]
  | switch (F G : Type) [Concrete F] [Concrete G]

structure MPC where prices : List (Cap × Price)
class Has (c : Cap) (M : MPC) where (price : Price) (mem : (c, price) ∈ M.prices)

def mul {F} [Concrete F] [Has (.on .mult F) M] (a b : D.S F) : Circ' D M (D.S F)
def rand (F) [Concrete F] [Has (.on .rand F) M] : Circ' D M (D.S F)        -- nothing fixes the field: pass it
def switch (G) [Concrete G] [Has (.switch F G) M] (a : D.S F) : Circ' D M (D.S G)
```

A circuit is generic over the fields it touches; `let a ← switch G b`
elaborates only if `M` offers the switch from `b`'s field to `G`:

```lean
def mulThenCompare {D : Domain} {M : MPC} {F G : Type} [Concrete F] [Concrete G]
    [Has (.on .mult F) M] [Has (.switch F G) M] [Has (.on .cmp G) M] [Has (.switch G F) M]
    (a b c : D.S F) : Circ' D M (D.S F) := do
  let ab ← mul a b                              -- in F
  let ab' ← switch G ab                         -- both conversions independent: one round
  let c' ← switch G c
  let bit ← lt ab' c'                           -- comparison is offered on G
  switch F bit                                  -- back in F

abbrev twoField : MPC := ⟨[(.on .mult Int, ⟨1, 2⟩), (.on .cmp Nat, ⟨2, 6⟩),
                            (.switch Int Nat, ⟨3, 8⟩), (.switch Nat Int, ⟨2, 4⟩), …]⟩
-- instantiates at F := Int, G := Nat; cost ⟨8, 28⟩, leak [], by rfl
```

Which field a value lives in is in its type, so an operation infers its
field from its argument and a mismatch is a type error. The MPC prices
per (feature, field): multiplication on two fields are separate entries,
and each direction of a switch has its own price.

Three consequences of "the field is the type":

* **Semantics is assembled from the entries.** `Cap.ideal` builds the
  ideal model of each capability from the instances the entry carries;
  `M.ideal` works for every `M` with no per-MPC code. A switch's ideal
  model is whatever conversion the protocol guarantees (integer value if
  in range, bit decomposition, embedding into an extension), stated once
  per pair of field types.
* **The price sits in the request.** `Has` carries the price as data and a
  request stores its `Has` evidence, so the cost model reads `h.price`
  with no lookup, no decidable equality on types, and no `⊤`: every
  well-typed circuit has a finite, total cost on its MPC.
* **Universe.** A request mentioning a field type lives in `Type 1`, so the
  core's `Sig` is universe-polymorphic; every single-field file stays at
  universe zero.

Each field has its own leakage type; `Model.mapLeak` puts a field's
leaked values on the shared `ℕ` alphabet through the `Encodable` instance
the entry carries. Coins need no conversion: each field's model draws
from the uniform distribution on that field (§6.4). This covers arithmetic/Boolean mixing (daBits become a
correlation across two fields), `ℤ/2^k ↔ 𝔽_p` switching, and
extension-field MAC checks.

### 2.10 One notion: functionalities and realisations

There is no distinction in kind between the MPC's multiplication and an
AES circuit. Both are **functionalities**: an interface with a `program`
and a `leak`. What differs is how they come to exist (`Functionality.lean`):

```lean
structure Functionality (L R : Type) where
  ops   : Sig
  model : Model ops L R                       -- program + leak, per operation

/-- `F` is realised over `G`: each op of `F` is a circuit over `G` computing
`F`'s program and revealing only what `F` declares, up to simulation. -/
structure Realization (F G : Functionality L R) where
  impl     : {β : Type} → F.ops β → Circ G.ops β
  realizes : Realizes impl G.model F.model

def Realization.id   (F) : Realization F F                      -- trusted: the MPC provides it
def Realization.comp : Realization F G → Realization G H → Realization F H   -- inlining; `Realizes` composes
def Realization.inl  (F G) : Realization F ⟨F.ops ⊞ G.ops, …⟩     -- feature inclusion
def Realization.sum  : Realization F G → Realization F' G → Realization ⟨F.ops ⊞ F'.ops, …⟩ G
```

Functionalities and realisations form a category: objects are
interfaces, morphisms are "implemented over", identities are trust, and
composition is inlining, with `Realizes` composing by the composition
theorem of §4.1. Everything earlier is an instance:

| Earlier notion                 | As a functionality / realisation                                   |
|--------------------------------|--------------------------------------------------------------------|
| primitive feature (`mult`, `rand`, `reveal`) | a functionality the MPC provides; realisation `id`; price on the MPC's list |
| MPC price list (§2.6)          | the set of functionalities realised by `id`, with their prices     |
| `Has τ σ`                      | the trivial realisation `inl : τ → τ ⊞ σ`                          |
| circuit with spec and declared leak | a one-operation functionality (`Functionality.ofCircuit`) realised over `σ` |
| gadget (§7)                    | such a realisation plus assumptions and a price; assumptions are the domain on which the program is defined |
| handler (`beaver`, `onPre`)    | a realisation of `Std` over `Pre`                                  |
| capability class (§2.5)        | several realisations of one functionality; instance choice picks one |
| derived price                  | the cost of `impl o` on the target; composes through `comp` as prices do |

The AES example in the file says it concretely. `AES` is a functionality
with one operation, program `aes k m`, empty leak. `cbc2` is written
against `[Has (AesOp D) σ] [Has (Lin D) σ]` and knows nothing about how
AES exists. Instantiation one: the MPC offers AES natively,
`Realization.id`. Instantiation two: `aesCircuit`, a circuit over the ABB
with one new obligation, its own `Realizes` proof. Either way `cbc2`'s
privacy is proved once, against `AES ⊞ ABB`, and `Hiding.transport` moves
it to whichever realisation is plugged in:

```lean
example (P : I → Circ ((AES F aes).sum (ABB F)).ops (F × F))
    (hP : Hiding (((AES F aes).sum (ABB F)).model.tagged ((AES F aes).sum (ABB F)).kind) P) :
    Hiding ((ABB F).model.tagged (ABB F).kind)
      (fun i => Circ.handle (Realization.sum (aesCircuit F aes impl h) (Realization.id (ABB F))).impl (P i)) :=
  Hiding.transport (Realization.sum … ).realizes P hP
```

So "the basic functionalities from which everything else is derived" is
literal: the trusted base is the set of `id` realisations, which is the
MPC's price list, and every other functionality is a composite of
realisations down to that base. A change of MPC changes the base; a change
of implementation changes one morphism; neither touches a caller's proof.

### 2.11 What this buys: circuits at the level of the functionality

A protocol is written against the functionalities it needs and proved
against their specifications. Every way of providing a functionality is
then a realisation that plugs in without touching the protocol or its
proof. For an AES-CBC protocol written in the AES-hybrid, the AES
functionality can be provided by:

| Realisation of `AES`                | What it is here                                                        | Trusted base                           |
|-------------------------------------|------------------------------------------------------------------------|----------------------------------------|
| arithmetic circuit over the ABB     | `Realization AES ABB`: S-boxes by inversion, linear layers free        | the ABB (the MPC's price list)         |
| Boolean circuit (garbled-circuit style) | `Realization AES BoolABB`: a circuit over `⟦ZMod 2⟧` with xor/and, plus a switch at the boundary if the caller's shares are arithmetic | the Boolean ABB, itself a primitive layer |
| hardware enclave                    | `Realization.id`: AES is a *primitive* functionality, priced on the list, with the leak the enclave is trusted to have (empty, or a declared side channel) | the enclave |

The protocol and its `Realizes` proof are identical in all three cases,
because the interface, program and leak of `AES`, is the contract. Two
consequences deserve to be said out loud:

* **The framework proves the hybrid layer.** What is verified is that the
  protocol realises its specification given ideal functionalities, and
  that realisations compose. That the garbling protocol realises the
  Boolean ABB, or that the enclave realises AES, is a statement about a
  protocol or a piece of hardware, outside this model and in its trusted
  base. The UC composition theorem is what joins the two, and it also
  says which security notion the whole inherits: perfect in the hybrid,
  composed with a computationally secure base, gives computational
  security overall.
* **Representations meet at the interface.** A Boolean realisation works
  on bit shares and an arithmetic caller holds field shares, so the
  realisation includes the conversion (§2.9, §6.5) and its price includes
  the switch. Alternatively the AES functionality is stated generic in the
  domain and each realisation fixes its own; either way the caller sees
  one `AesOp`.

The same holds one level up: the CBC functionality of `AesHybrid.lean` is
itself an interface, and a higher protocol written against `CBC` never
learns whether it is running on the hybrid circuit, on a direct
implementation, or on hardware.

**Terminology.** The latency notion is called *delay*: the length of the
critical path through a circuit's dependency graph under the per-operation
latencies of an MPC. Rounds are its unit. "Depth" is the special case where
every operation has latency one.

### 2.12 Interfaces and meaning: when a circuit has semantics

A signature is a *vocabulary*. `MulTriple D` is one request, `get`, whose
answer has type `D.S × D.S × D.S`; `Has (MulTriple D) σ` says that request is
available to circuits over `σ`. Nothing else: no distribution, no leak, no
spec. The same holds for every feature. `Has (Mult D) σ` does not say that
`mult` multiplies. So the type of a circuit,

```lean
def mulBeaver [Has (Lin D) σ] [Has (Reveal D) σ] [Has (MulTriple D) σ] [Mul D.F] (x y : D.S) : Circ σ D.S
```

reads "written using the interfaces of the linear, reveal and triple
functionalities", and a `Circ σ α` is a syntax tree: which requests are
made, in what order, and how each continuation depends on the answers.
Output, leakage, delay and cost are all `run` under a model (§3), so an
unmodelled circuit has a shape and nothing more.

A *functionality* is an interface together with its meaning: a
`Model`, program and leak (`Functionality.lean` bundles the two, with
the request kinds of §4.1). The library fixes **one ideal model per
interface name**: `MulTriple.ideal` says `get ↦ (a, b, a·b)` with `(a, b)`
uniform on `F²` and nothing leaked, `Mult.ideal` says `mult ↦ a·b`,
`Reveal.ideal` says `reveal ↦ x`, leaking `[x]`. That binding is what the
name promises, and it is why the interface must be named after the
functionality it is the interface of: `MulTriple`, not "triple", and
`SquarePair` and `DoubleSharing` are distinct interfaces although their
responses have the same type (§6.1).

"Instantiating" an interface therefore means two different things, and
only one of them is needed for semantics:

* **Giving the interface its ideal model.** This is what a circuit's
  semantics needs, and it is not a per-MPC choice. On the price-list
  route (§2.6, `Features.lean`) it happens by name: `Feature.ideal
  .mulTriple := MulTriple.ideal`, and a circuit `Circ' D M` has its
  semantics `M.ideal` the moment it typechecks. Every MPC that offers
  `.mulTriple`
  offers *that* functionality; the price list only says what it charges
  and cannot redefine what it means.
* **Realising the interface** by a protocol, or by a circuit over other
  features (`onPre`, `aesByCircuit`). This never touches semantics. The
  circuit is a program in the hybrid where the interface is ideal, its
  meaning is with respect to the ideal model, and a realisation carries
  the theorems across (§4.1, `handle_realizes`). That is the UC reading:
  a hybrid protocol is a program in the `F`-hybrid, and `F`'s ideal
  functionality is part of its definition.

This is the invariant stated in §7 from the other side: **a circuit has
semantics regardless of the MPC, but a cost only once an MPC is fixed.**
Semantics needs the functionality (fixed per name by the library); cost
needs the price list.

What the core keeps open, by leaving the model a parameter of `run`, is
the ability to interpret the same syntax in other ways: evaluation at
`Id` for `rfl`, the clock model for delay, a hybrid model in which a
callee is abstract, or a deliberately wrong model to state a
counterexample (`BadMulTriple`, `Beaver.lean`: same interface, `a = b`,
still correct, not hiding). Those are other *interpretations* of one
program, not other meanings of "triple", and every theorem names the
model it is about, so nothing proved against `MulTriple.ideal` can be
mistaken for a statement about another model. If the canonical model
should also appear in the types of core circuits, the change is a
functionality-indexed `Has` on top of `Functionality`, the feature-name
route already being that for price lists (decision 013).

## 3. Semantics

### 3.1 Models: return values and leakage, in a monad

```lean
structure Model (σ : Sig) (L : Type) (m : Type → Type) where
  program : {α : Type} → σ α → m α           -- what the operation returns, in `m`
  leak    : {α : Type} → σ α → α → List L    -- what the adversary sees: request and response
```

A model says, for each request, what comes back and what is observed.
The monad `m` is the one design decision of this section, and it is what
removed the coin tape:

* `m := PMF` (Mathlib's probability mass functions) is **the semantics**.
  `rand` is `PMF.uniformOfFintype F`; a Beaver triple is the image of a
  uniform draw from `Fin 2 → F`; a run is a distribution over
  (output, revealed values). Privacy is stated here and nowhere else.
* `m := Id` is **evaluation**. Deterministic features (`Lin`, `Mult`,
  `Reveal`, `Cmp`, …) are modelled at `Id` once and lifted into any
  monad by `Model.lift`, whose program is `pure`. Coin-free circuits
  compute output, leakage and cost by `rfl`/`decide`, and `dist_lift`
  says their `PMF` semantics is the point at that evaluation, so `rfl`
  proofs transfer to the semantics.
* `m := Sched := StateT Clock Id` is **scheduling**: the timed domain of
  §3.5, where a clock records what has been revealed.

Leakage is a function of the request *and* the response: for `reveal x`
either would do; for a public coin only the response carries the value.

The *ideal* domain identifies shares with values, `Domain.ideal F := ⟨F, F⟩`.
The ideal model of `Std` is the obvious one: `mult a b ↦ pure (a * b)`,
silent; `reveal x ↦ pure x`, leaks `[x]`. `Rand.ideal` draws
`uniform F`; `MulTriple.ideal` samples its correlation from a *jointly*
uniform `Fin c.k → F` (§6.1); `RandNZ.ideal` draws a uniform nonzero
element, for gadgets that mask by multiplication. There is no tape and
no coin index: each draw is a fresh `bind`, and `k` draws are one draw
from `F^k` (`seqUniform_eq_uniform`, §4.1). Models of sums are sums of
models, so the model of a functionality is assembled feature by feature,
like the signature.

The models carry no state of their own. That is what makes running
`c >>= k` the same as running `c` and then `k` in *every* lawful monad
(`run_bind`), and that one law is what every composition theorem rests on.

### 3.2 Cost: an additive monoid, and a price per operation

```lean
structure Price where (delay : Nat) (comm : Nat)      -- what an MPC charges for a feature

structure CostModel (σ : Sig) (C : Type) where
  op : {α : Type} → σ α → C                            -- price per call, in an `AddMonoid C`
```

Costs add along a run; the carrier is any Mathlib `AddMonoid`: `ℕ` for
communication, `WithTop ℕ` when unsupported operations are priced `⊤`
("runs on this MPC" is "has finite cost", `Has.finite`, `cost_finite`),
`Unit` for none. Delay is *not* a cost in this sense: it is computed
from data dependencies in the timed domain (§3.5), and a `Price` feeds
its `delay` to that domain and its `comm` to the additive model.

An MPC prices every feature with a `Price`. Four independent
multiplications written one after another have delay 1 and
communication 8; four dependent ones have delay 4 and communication 8
(`Features.lean`). Delay does not stack, and nothing has to say so per
circuit: it falls out of the dependency graph.

"Score different sub-functionalities differently" is a price list. Several
lists coexist for one feature set, and for sums of signatures cost models
are sums of cost models:

| Feature  | honest-majority rounds | preprocessing rounds | online triple generation | `total` (openings) |
|----------|-----------------------:|---------------------:|-------------------------:|-------------------:|
| `Lin`    | 0                      | 0                    | 0                        | 0                  |
| `Mult`   | 1                      | (via `MulTriple`)    | (via `MulTriple`)        | 1                  |
| `Reveal` | 1                      | 1                    | 1                        | 1                  |
| `Rand`   | 0 (PRSS)               | 0                    | 1                        | 0                  |
| `MulTriple` | —                   | 0 (precomputed)      | 2                        | 0                  |
| `Cmp`    | e.g. 3                 | e.g. 2               | e.g. 4                   | e.g. 5             |

The sketch has `Pre.timed F 1 0` and `Pre.timed F 1 2` for the two
`MulTriple` columns; the same Beaver circuit has delay 1 under the first and
3 under the second, both by `rfl`.

### 3.3 The interpreter

```lean
def run (M : Model σ L m) (K : CostModel σ C) : Circ σ α → m (α × Trace C L)
  | .pure a   => pure (a, Trace.zero)
  | .call o k => do let x ← M.program o
                    let r ← run M K (k x)
                    pure (r.1, Trace.seq ⟨K.op o, M.leak o x⟩ r.2)      -- cost adds, leaks append

def output (M : Model σ L Id)  (c) : α        := (Id.run (run M .unit c)).1
def leak   (M : Model σ L Id)  (c) : List L   := (Id.run (run M .unit c)).2.leak
def cost   (M : Model σ L Id)  (K) (c) : C    := (Id.run (run M K c)).2.cost
def dist   (M : Model σ L PMF) (c) : PMF (α × List L) := (fun p => (p.1, p.2.leak)) <$> run M .unit c
```

One interpreter, written once for any monad, yields every observable.
Cost is orthogonal to semantics by construction: `output` and `leak` are
computed under the unit cost model and provably do not depend on the cost
model (`run_fst`), and the cost model never sees values. The only
coupling is control flow: an `if` on an opened value decides which
branch's cost is paid, so cost depends on the *model* exactly as far as
the circuit's shape depends on opened data. For structurally scheduled
circuits it does not depend on it at all; in general it is a
distribution (`costDist`), as it should be.

The laws, proved once by induction on the free monad:

```lean
run_bind  : run M K (c.bind k) = do r ← run M K c; s ← run M K (k r.1); pure (s.1, r.2.seq s.2)  -- any lawful `m`
run_lift  : run (M.lift m) K c = pure (Id.run (run M K c))          -- a coin-free run is a point
dist_lift : dist (M.lift PMF) c = pure (output M c, leak M c)       -- so `rfl` at `Id` is a theorem at `PMF`
dist_bind : dist M (c.bind k)  = do r ← dist M c; s ← dist M (k r.1); pure (s.1, r.2 ++ s.2)
dist_call : dist M (.call o k) = do x ← M.program o; r ← dist M (k x); pure (r.1, M.leak o x ++ r.2)
```

A concrete circuit that draws coins has its distribution *computed* by
`simp` with the run lemmas: `dist (Pre.ideal F) (onPre (mul x y))`
unfolds to "draw `(a, b)` uniform on `F²`, output `x·y`, reveal
`(x − a, y − b)`" in one call (`Glean.lean`, `beaver_hiding`), and the
proof of hiding is then the mask lemma. The tape semantics that used to
be needed for evaluation is gone: `Model.lift` and `dist_lift` give
evaluation by `rfl` for exactly the circuits where evaluation makes
sense, and `simp` does the rest.

Structured share types (`Vector D.S n`, records of shares) need nothing
new: they are Lean values holding handles. A Clean-style `SharedType T`
class mapping `T D.F ↔ T D.S` is worth adding for I/O ergonomics
(`open` a whole struct, `const` a whole struct), but it is sugar.

### 3.4 Delay and communication are separate theorems, and both compose

A price list carries both numbers per feature, but theorems mention one
resource at a time. `delayOn M c` runs the circuit in the timed domain
with the latencies of the timed model `M`, and `comm M b c` runs it under
the additive cost model with per-operation bandwidths `b`; an MPC's list
yields `M.timed` and `M.bandwidth` separately (`Cost.lean`). `fourPar`
is 1 round and 8 units of communication; `fourSeq` is 4 rounds and 8
units; each is its own `rfl`.

**Composition for cost** has the same shape as composition for privacy.
Call an implementation *priced* under `K` if each operation's circuit has
a cost independent of its arguments and coins (structurally scheduled):

```lean
def PricedImpl (Mσ) (impl : {β} → τ β → Circ σ β) (K : CostModel σ C) (p : Costs τ C) : Prop :=
  ∀ o, costDist Mσ K (impl o) = pure (p o)

theorem cost_handle (h : Realizes kσ kτ impl Mσ Mτ) (hp : PricedImpl Mσ impl K p) (P : Circ τ α) :
    costDist Mσ K (Circ.handle impl P) = costDist Mτ ⟨p⟩ P
```

Inlining a priced implementation into any caller costs what the caller
costs with each abstract operation priced at its implementation's cost
(proved, `Cost.lean`: by induction on the caller, `run_bind`, and the
fact that a realisation's result is distributed as the abstract program's).
`comm_handle` is its communication instance, and at the level of
functionalities a realisation's *derived price* composes along
`Realization.comp` (`Realization.comp_derivedPrice`), one `cost_handle`
per level. So a
protocol's round and communication complexity are stated once in the
hybrid with abstract prices, and instantiating AES by a circuit
substitutes that circuit's cost for the abstract price, with no new
analysis of the protocol.

**Delay under eager scheduling compose exactly too, with one
refinement.** Under dependency tracking (§3.5) an abstract operation must
not be modelled by a single latency: that serialises its whole
implementation behind all of its inputs, and an implementation with a
"late" input (`mulAdd a b c = a·b + c` needs `c` only after the
multiplication) would then be over-counted. Model it instead by its
**timing profile**, the longest path from each input to the output inside
the implementation (plus `d₀` for input-free sources such as
preprocessing):

    ready(out) = max (d₀, max_i (ready(in_i) + d_i))

With profiles, the caller's round count equals the inlined circuit's,
because the longest path through a substituted dependency graph
decomposes at the substitution boundary. `Timing.lean` checks the
three numbers on a caller whose `c` arrives at round 1: atomic model 2,
profiled model 1, inlined circuit 1. A single latency is the profile with
all `d_i` equal, which is exact for native operations like `mult` that do
wait for all inputs. So the recommended round semantics is eager
scheduling with profiles: no `∥` to write, no upper-bound caveat, and
communication and rounds both compose exactly.

### 3.5 Delay is computed, not proved, and needs no `∥`

Round complexity is a pass over the circuit, and the user proves nothing
for a concrete circuit: the interpreter is the pass and `rfl` runs it.
There is no parallel node in the circuit language (decision 002):
parallelism is **computed from data dependencies**.

**Dependency tracking (`Timing.lean`).** Let every share carry the round
at which it is available. An operation's result is ready at
`max (inputs' ready times, clock) + latency`, and the round complexity of
a circuit is the ready time of its output: the critical path of the data
dependency graph. This is a *second domain*, because circuits are
polymorphic in the domain, and a second monad, because the clock is state:

```lean
structure Timed (F : Type) where (val : F) (time : Nat)
abbrev Domain.timed (F : Type) : Domain := ⟨F, Timed F⟩     -- shares are timed, clear values plain
structure Clock where (clock : Nat := 0) (revealed : Nat := 0)
abbrev Sched := StateT Clock Id                             -- the scheduling monad

def Mult.timed (ℓ) : Model (Mult (Domain.timed F)) F Sched where
  program | .mult a b => Timed.after [a.time, b.time] ℓ (a.val * b.val)   -- max of inputs and clock, plus ℓ
def Reveal.timed (ℓ) … program | .reveal a => fun s => (a.val, { s with revealed := max s.revealed (… + ℓ) })

def delayOn (M : Model σ L Sched) (c : Circ σ (Timed F)) : Nat := (Sched.output M c).time
```

With this, sequential `do`-code gets the parallel count and no `∥` is
needed anywhere:

```lean
def mul4seq (a b c d : D.S) : Circ σ D.S := do
  let ab ← mul a b
  let cd ← mul c d          -- independent of ab: the pass sees it
  mul ab cd
-- rounds = 2 (rfl); the chain x·b·c·d is 3; the product tree with plain binds is its depth
```

Clear values stay plain, so generic circuits branch on them as usual; what
the dependency graph cannot see about them, two clocks in the scheduling
state cover. The *reveal clock* is the latest time at which anything was
revealed, and any operation with a clear argument (`const`, `smul`)
inherits it, since clear computation is opaque: a value revealed at
round 2, multiplied in the clear and inserted back with `const`, carries
round 2 into whatever uses it (`revealThenUse`, 3 rounds by `rfl`). The
*control clock* handles a branch on a revealed value whose arms do not
data-depend on it: the circuit says `barrier`, which raises the control
clock to the reveal clock, so everything issued afterwards is scheduled
after the values it branched on (`binarySearch`: 3 levels × 4 rounds).
Reveal itself does not raise the control clock, so independent reveals
share a round (Beaver's two openings). Semantics is untouched: the timed
model computes the same values, only tagged, and coins get a dummy
value, which delay never depends on.

For families ("`prodAll` on `n` elements is `⌈log₂ n⌉` rounds") the generic
technique is an induction using `run_bind` and `omega`, with the gallery
as templates. Proof-by-evaluation uses `rfl` and kernel `decide` only;
`native_decide` is never used.

## 4. Properties and the shape of proofs

All three are stated against a model, and for concrete circuits all three
are proved by `rfl` / `decide`: the interpreter just runs.

```lean
-- correctness
example (a b c : F) : output (Std.ideal F) (mul3 a b c) = a * b * c := rfl
-- rounds (timed domain, inputs at round 0)
example (a b c : F) : delay F (Std.timed F) (mul3 ⟪a⟫ ⟪b⟫ ⟪c⟫) = 2 := rfl
example : delay F (Std.timed F) (prodTree depth2Tree) = 2 := rfl   -- 4 leaves, plain binds
-- leakage is computed, not asserted
example (a b : F) : leak (Std.ideal F) (openMul a b)  = [a * b] := rfl
example (a b : F) : leak (Std.ideal F) (leakyMul a b) = [a, b]  := rfl
```

### 4.1 Privacy: simulation at the level of the functionality

**Setting.** Every functionality has two parts, `program` (what it
computes and returns) and `leak` (what the adversary observes when it is
invoked): `rand` has an empty leak, `reveal` leaks its value, `mult` leaks
nothing. A circuit is a program in the functionality-hybrid model, and we
prove it secure *there*. This is the arithmetic-black-box methodology of
Damgård–Nielsen and SPDZ: the UC composition theorem turns "the circuit
is secure given an ideal ABB" plus "the protocol realises the ABB" into
security of the whole, so the MPC protocol is never modelled here. What
remains to be simulated is exactly what the circuit chooses to reveal,
and the values inside shares (`⟦a⟧`, notation for a share of `a`) are
hidden by fiat.

**One shape of statement.** The semantics of a circuit is a
distribution over (output, revealed values), `dist M c : PMF (α × List L)`.
Every privacy statement is

> *X can be simulated given Y*

meaning the joint distribution of `(Y, X)` equals that of `(Y, Sim Y)`
with the simulator's coins fresh, i.e. one equation between `PMF`s. The
top-level instance (`Glean.lean`):

```lean
def Hiding (M : Model σ L PMF) (c : I → Circ σ α) : Prop :=
  ∃ Sim : α → PMF (List L), ∀ i,
    dist M (c i) = do let y ← Prod.fst <$> dist M (c i); let s ← Sim y; pure (y, s)

def HidingStat (M) (ε : ENNReal) (c) : Prop :=          -- within ε in total variation
  ∃ Sim, ∀ i, PMF.statDist (dist M (c i)) (do …) ≤ ε
```

Read it as: draw the output as the circuit draws it, let a simulator
that sees only the output invent the revealed values, and the pair must
be distributed as the real run. There is no coin tape, no bijection and
no re-randomisation in the definition; the simulator's independence from
the output is what `bind` means. The usual instances:

| X (to simulate)       | Y (given)                          | reads as                                   |
|-----------------------|------------------------------------|--------------------------------------------|
| revealed values       | output                             | hiding: reveals nothing beyond the output  |
| revealed values       | output, corrupt inputs             | hiding against a corrupt coalition         |
| revealed values       | nothing                            | the reveals are pure noise (Beaver, a2b)   |
| revealed values       | output, `argmax`                   | declared extra leakage                     |
| concrete view         | abstract (declared) view           | a realisation, the compositional notion    |
| contents of shares    | nothing                            | trivially, shares are hidden by fiat       |

**Why the masks must be jointly uniform, and why that is a theorem
here.** A simulator has to produce the *whole list* of revealed values
with the right joint distribution, so every mask argument needs the
whole vector of masks a run draws to be uniform on `F^k`, not each
coordinate uniform on `F`. Coordinate-wise uniformity is not enough:
Beaver with `a = b` (each uniform) reveals `x − a` and `y − a`, whose
difference is `x − y`. Pairwise independence is not enough either:
`r₁, r₂` independent uniform and `r₃ := r₁ + r₂` are pairwise
independent and each uniform, but revealing `x − r₁`, `y − r₂`,
`z − r₃` publishes `x + y − z`. Only joint uniformity of the mask vector
(equivalently, mutual independence of the masks) makes the revealed
vector the image of a uniform vector under a bijection, which is the one
fact every proof uses. In a tape semantics this is an *assumption* about
the measure on tapes, and the proof rule "a bijection on tapes preserves
it" is false for infinite tapes and a counting argument for finite
prefixes. In the `PMF` semantics it is a *theorem*: each coin is a fresh
`bind` of `uniform F`, and

```lean
theorem uniform_prod : (do a ← uniform α; b ← uniform β; pure (a, b)) = uniform (α × β)
theorem seqUniform_eq_uniform : seqUniform F n = uniform (Fin n → F)     -- n fresh draws = one draw from Fⁿ
```

(`Privacy.lean`). Correlations draw their `k` coins as one uniform
`Fin k → F` outright (§6.1), so a triple's `(a, b)` is jointly uniform by
definition. `Beaver.lean` shows all of this on multiplication from
triples: one triple (`mulBeaver_hiding`, a bijection of `F²`), two chained
multiplications (`mul3Beaver_hiding`: two calls are one draw from
`F² × F²` by `uniform_prod`, then a bijection of `F⁴`), and the
counterexample `BadMulTriple` whose `a` and `b` are each uniform but equal:
the circuit is still perfectly correct on it, and provably not hiding
(`mulBeaver_bad_not_hiding`, the opened pair publishes `x − y`). This is the whole reason there is no tape and no bijection on
tapes anywhere: the only bijections in the development are on finite
types, in the one lemma that follows.

**The generic per-operation technique: the mask lemma.** Almost every
revealed vector in an MPC circuit is `v = f(secrets, masks)` with fresh
masks. If, for every value of the secrets, `masks ↦ v` is a bijection of
`F^k`, then `v` is uniform and independent of the secrets: the simulator
draws `v` fresh. Packaged once, as a fact about Mathlib's uniform
distribution:

```lean
theorem uniform_map_equiv (e : α ≃ β) : (uniform α).map e = uniform β
```

with the bijections coming from Mathlib's `Equiv` library: `Equiv.subLeft x`
for `a ↦ x − a`, `Equiv.mulLeft₀ x hx` for `s ↦ x·s` on the nonzero
elements, `Equiv.prodCongr` and `piFinTwoEquiv` to assemble vectors. The
proof of Beaver's hiding (`beaver_hiding`) is: `simp` unfolds the run to
"draw `v` uniform on `Fin 2 → F`, output `x·y`, reveal
`(x − v 0, y − v 1)`"; `ring` closes the output; `uniform_map_equiv` with
`(v 0, v 1) ↦ (x − v 0, y − v 1)` closes the reveals. Inversion by a
nonzero mask (`invertGadget`) is the same three steps with `mulLeft₀`.
This lemma is the one-time-pad lemma, the `rnd` rule of EasyCrypt, the
random-mask elimination step of maskVerif, and the affine treatment of
random values in λ_obliv, in one statement. It is also what a tactic
should automate: a leakage entry of the form `x ± r` or `x · r` with a
fresh mask `r` is discharged by constructing the shift or scale bijection.

**The adversary's view is the tagged trace.** The adversary also sees
*which* operations are invoked (the parties execute them, and the program
is public). So the view of a run is, per request, the request's public
*kind* together with what the functionality declares for it:

```lean
def Model.tagged (Mτ : Model τ L m) (kind : {β} → τ β → K) : Model τ (K × List L) m :=
  { program := Mτ.program, leak := fun o y => [(kind o, Mτ.leak o y)] }
```

`dist (Mτ.tagged kind) c` is the distribution of (output, view). The kind
carries no payload (the request's shares never appear), and it is what
lets a simulator know that a `mult` happened without seeing its inputs.

**Composition: a verified circuit is a functionality.** A primitive
operation has a `program` and a `leak`. A verified circuit gets the same
two things: its `program` is its spec, and its `leak` is its *declared*
leakage, the `view` of its gadget. Callers treat the circuit as one more
operation of an abstract signature, prove their own privacy against that
abstract model, and never look inside. The definitions and the theorem
that make this sound (`Privacy.lean`, `Compose.lean`), all proved:

```lean
/-- `impl` realises the abstract `Mτ` on the concrete `Mσ`: for each request, the concrete
(response, view) is the abstract response with the view simulated from the abstract record. -/
def Realizes (kσ) (kτ) (impl : {β} → τ β → Circ σ β) (Mσ : Model σ L PMF) (Mτ : Model τ L PMF) : Prop :=
  ∃ Sim : Kτ → List L → PMF (List (Kσ × List L)), ∀ o,
    dist (Mσ.tagged kσ) (impl o) = do let y ← Mτ.program o; let s ← Sim (kτ o) (Mτ.leak o y); pure (y, s)

/-- Inlining realised operations into any caller: the concrete run is the abstract run with each
declared record replaced by its simulation. -/
theorem handle_realizes (h : ∀ o, dist (Mσ.tagged kσ) (impl o) = …Sim…) (c : Circ τ α) :
    dist (Mσ.tagged kσ) (Circ.handle impl c) = do let r ← dist (Mτ.tagged kτ) c; let s ← simList Sim r.2; pure (r.1, s)

theorem Realizes.comp : Realizes kτ kρ f Mτ Mρ → Realizes kσ kτ g Mσ Mτ → Realizes kσ kρ (fun o => handle g (f o)) Mσ Mρ
theorem Realizes.id   : Realizes k k (fun o => Circ.op o) M M
theorem Hiding.transport : Realizes kσ kτ impl Mσ Mτ → Hiding (Mτ.tagged kτ) P → Hiding (Mσ.tagged kσ) (fun i => handle impl (P i))
theorem output_transport : Realizes … → Prod.fst <$> dist Mσ (handle impl c) = Prod.fst <$> dist Mτ c
```

Read `Realizes` as: the simulator is given only the abstract record
(kind and declared leak), never the response unless the functionality
leaks it and never the request's payload, and must reproduce the
concrete view jointly with the response. `handle_realizes` is the UC
composition theorem at the level of this semantics: induction on the
caller's free-monad trace, `dist_bind` at each `call`, the realisation
equation for that call, and one commutation of independent draws
(`PMF.bind_comm`: the simulator's coins for this call do not interact with
the rest of the run). `Realizes.comp` is why functionalities and
realisations form a category (§2.10); `Hiding.transport` and
`output_transport` are the payoff for a caller's privacy and correctness.

Worked instance: the Beaver handler realises `Std` on `Pre`
(`preHandler_realizes`, `Privacy.lean`): the simulator for `mult`
produces the records of a Beaver run with a fresh uniform pair in the two
reveals; `lin` and `reveal` replay their record. Hence *every* circuit
proved hiding on the arithmetic black box is hiding on the preprocessing
functionality with Beaver inlined, with no new proof (`Compose.lean`,
last example), and the same for a2b via edaBits realising an `A2B`
operation with empty leak, `binarySearch` realising a lookup operation
whose declared leak is its public output, or an entire AES functionality
realised by a circuit (`AesHybrid.lean`, `cbcOverABB`).

So privacy proofs compose exactly as programs do: prove each gadget once
against its declared leak, wrap it as an operation (`Gadget.toModel`:
`program := its output distribution`, `leak := view`), and prove callers
against the abstract model. Nothing is redone when a callee's
implementation changes, as long as the new one still `Realizes` the same
abstract operation. This is what Clean's local subcircuit proofs become in
MPC: the local proof is a realisation, and the abstract operation is the
interface. Sequential composition of two gadgets needs no primitive of
its own: it is a two-call caller in the hybrid.

**A subtlety about transitivity.** "X given Y" is *not* transitive in
general: from "X simulatable given Y" and "Y simulatable given Z" one
cannot conclude "X given Z" (take `Z` a coin, `Y = ()`, `X = Z`). The
compositional statements are therefore always about the *joint* view:
`Realizes` reproduces (response, view) jointly, and `Hiding.transport`
composes two joint statements rather than chaining two conditionals.
This is the same reason UC keeps the environment in the definition: what
is simulated is the whole view, not one projection at a time. It is also
why the compositional notion conditions on the callee's *declared leak*
and not on its output: a sub-gadget's output is a hidden handle nobody
sees, and a simulator that needed it could not be run by the caller's
simulator.

**Statistical privacy** is the same statement up to `ε` in total
variation (`PMF.statDist`, `HidingStat`, `RealizesStat`); a gadget
carries its `ε`, zero for perfect ones (§7). Zero distance is equality
(`PMF.eq_of_statDist_eq_zero`), so perfect gadgets prove the equation.
See `decisions/009-statistical-privacy.md` for what remains (the
contraction of `bind` in total variation, which makes `ε` add under
composition).

**Related work that shaped this.**

* Damgård & Nielsen 2003, and SPDZ (Damgård, Pastro, Smart, Zakarias
  2012): the arithmetic black box and circuits as programs over it.
  Damgård, Fitzi, Kiltz, Nielsen, Toft 2006 and Catrina & de Hoogh 2010:
  the standard "the opened value is uniform because the mask is fresh"
  privacy arguments for ABB sub-protocols, which `Masked` packages.
* Canetti 2001 (UC), Lindell "How to simulate it": the real/ideal
  definition `Realizes`/`Hiding` specialises, and the composition theorem that
  justifies never modelling the protocol.
* Haagh, Karbyshev, Oechsner, Spitters, Strub 2018 (EasyCrypt, MPC over an
  ABB with active security); Almeida, Barbosa, Barthe, Pacheco, Pereira,
  Portela 2018 on connecting ideal-world leakage of ABB circuits to
  real-world Sharemind/Bristol leakage; Pettai & Laud 2015 on
  *automatically* proving privacy of ABB protocols by dependency analysis
  of published values, which is the automation target above.
* Barthe, Belaïd, Dupressoir, Fouque, Grégoire, Strub 2015/2016
  (maskVerif, t-NI/t-SNI): "a set of observations is simulatable from a
  subset of inputs" as a per-gadget, composable notion, proved by
  random-mask elimination; the closest formal ancestor of `Realizes`.
* Darais, Sweet, Liu, Hicks 2020 (λ_obliv): uniform random values as
  affine resources in a type system, giving probabilistic obliviousness
  by typing; the discipline a `masked` tactic would check.
* Barthe, Grégoire, Zanella-Béguelin (EasyCrypt) and Barthe et al. 2017
  on couplings: bijection-based equidistribution as the proof rule.
  Brzuska et al. 2018 (state-separating proofs) and SSProve 2021:
  modular packages with local simulators composed by a hybrid argument,
  which is the shape of `Gadget` plus `handle_realizes`. IPDL (Gancher et al.
  2023): equational simulation proofs for protocols, including MPC.
* Wysteria / Wys★ (Rastogi, Hammer, Hicks 2014; Rastogi, Swamy, Hicks
  2019) and Viaduct (Acay et al. 2021): mixed-mode MPC languages whose
  security is stated over an ideal functionality, with information-flow
  labels doing the bookkeeping our `Has`/domain typing does.

### 4.2 Generic circuits, generic theorems

Circuits are polymorphic in `σ` and `D`; theorems can be too. Round bounds
are best stated for *any* cost model that prices the features a certain way:

```lean
theorem inner_rounds (κ : {α : Type} → σ α → Nat)
    (hlin : ∀ {α} (o : Lin D α), κ (Has.inj o) = 0)
    (hmul : ∀ a b, κ (Has.inj (Mult.mult a b)) = 1) (xs ys : List D.S) :
    cost M ⟨.rounds, κ⟩ (inner xs ys) = min (xs.zip ys).length 1
```

This reads "in any model where linear ops are free and multiplication is
one round, inner product is one round", and it holds for every `M`.

## 5. Composition

Proofs about `bind` reduce to proofs about the pieces, in any lawful monad:

```lean
run_bind  : run M K (c.bind k) = do r ← run M K c; s ← run M K (k r.1); pure (s.1, r.2.seq s.2)
dist_bind : dist M (c.bind k)  = do r ← dist M c; s ← dist M (k r.1); pure (s.1, r.2 ++ s.2)
dist_call : dist M (.call o k) = do x ← M.program o; r ← dist M (k x); pure (r.1, M.leak o x ++ r.2)
dist_lift : dist (M.lift PMF) c = pure (output M c, leak M c)
```

(all by induction on `c`; `run_bind` needs only that costs form a
monoid). With these as `simp` lemmas, the distribution of a concrete
circuit normalises to closed form (a uniform draw, then a point), and
hiding proofs reduce to the mask lemma.

**Handlers.** `Circ.handle : ({β} → τ β → Circ σ β) → Circ τ α → Circ σ α`
implements every op of `τ` by a circuit over `σ`. The sketch does this for
multiplication:

```lean
def beaver [Has (Lin D) σ] [Has (Reveal D) σ] [Has (MulTriple D) σ] [Mul D.F] :
    {β : Type} → Mult D β → Circ σ β
  | _, .mult x y => do
    let (a, b, c) ← mulTriple
    let u₁ ← sub x a
    let e ← reveal u₁
    let u₂ ← sub y b
    let d ← reveal u₂                   -- independent of the first reveal: same round (§3.5)
    ... -- x·y = c + e·b + d·a + e·d, linear from here

def onPre : Circ (Std D) α → Circ (Pre D) α :=       -- Std circuits run on Pre
  Circ.handle fun o => match o with
    | .inl o => Circ.op o | .inr (.inl o) => beaver o | .inr (.inr o) => Circ.op o
```

This is the mechanism for

* realising a feature on top of others (`Mult` as above; `Cmp` via bit
  decomposition; `Rand` via `MulTriple`), and
* deriving cost, output and leakage of the composite from those of the
  handler: cost of `handle h c` under `K` equals cost of `c` under the
  model that prices each `o` at the cost of `h o` (`cost_handle`); the
  output distribution is unchanged (`output_transport`); the view of
  `handle h c` is the view of `c` with each record simulated
  (`handle_realizes`), so a realising handler composed with a hiding
  circuit is hiding (`Hiding.transport`). These are the theorems that
  make the library modular, and they are proved (`Compose.lean`,
  `Cost.lean`).

`Circ.weaken` (a circuit over fewer features runs on more) is the
degenerate handler.

## 6. Correlated randomness

Everything an MPC hands out at random is one of three things, and each has
one place in the design.

### 6.1 Primitive correlations: a function of fresh coins

A correlation is a deterministic function of `k` uniform coins. That is the
whole definition. Each correlation is its own interface, named after the
functionality (decision 013), and `Correlation` is the generic way to give
it a model:

```lean
structure Correlation (R T : Type) where
  k     : Nat
  build : (Fin k → R) → T

def Correlation.sample (c : Correlation R T) : PMF T :=
  (uniform (Fin c.k → R)).map c.build            -- the k coins are drawn *jointly* uniform on Rᵏ

/-- A multiplication triple: the interface. -/
inductive MulTriple (D : Domain) : Sig where
  | get : MulTriple D (D.S × D.S × D.S)

/-- Its ideal model: sample the correlation, leak nothing. -/
def MulTriple.corr : Correlation F (F × F × F) := ⟨2, fun x => (x 0, x 1, x 0 * x 1)⟩
def MulTriple.ideal : Model (MulTriple (.ideal F)) L PMF where
  program o := match o with | .get => (MulTriple.corr F).sample
  leak _ _ := []
```

The response type describes a sample in terms of the domain, so the same
interface works for every representation of shares; `build` is written
once, at the ideal domain, where a share is its value. `SquarePair` and
`DoubleSharing` have the same response type and are different interfaces:
a circuit asking for one cannot be handed the other.

| Correlation        | `T D`                      | coins | `build`                                  |
|--------------------|----------------------------|------:|------------------------------------------|
| random share       | `D.S`                      | 1     | `x 0`                                    |
| square pair        | `D.S × D.S`                | 1     | `(x 0, x 0 * x 0)`                       |
| Beaver triple      | `D.S × D.S × D.S`          | 2     | `(x 0, x 1, x 0 * x 1)`                  |
| double sharing     | `D.S × D.S` (or `D.S × D.S₂`) | 1  | `(x 0, x 0)`                             |
| matrix triple      | `Mat n m D.S × Mat m k D.S × Mat n k D.S` | nm + mk | `(A, B, A·B)`               |
| random bit         | `D.S`                      | 1 bit | needs the bit alphabet, §6.4             |
| daBit              | `D.S × D.B`                | 1 bit | `(embed b, b)`, cross-domain, §6.5       |
| random permutation | `Perm n D.S`               | Fisher–Yates | needs a `Fin`-valued alphabet, §6.4 |

The double sharing row makes a general point: in the black box, `[r]_t` and
`[r]_2t` are the same value seen twice, because sharing degree is not
observable there. If a circuit must respect degrees (it may only add
same-degree shares, it needs a `reduce` operation to go from `2t` to `t`),
give the domain two share types, `D.S` and `D.S₂`, and type the operations
accordingly. The ideal model still identifies the values; the types stop
the circuit from misusing them. The same move handles authenticated
versus unauthenticated shares, or shares over different rings.

### 6.2 Assembling correlations: the offline phase is a handler

A correlation that the MPC does not hand out natively is *assembled* from
ones it does, and the assembly is a handler in the sense of §5:

```lean
/-- Triples from random shares and one secure multiplication. -/
def tripleFromRand [Has (Rand D) σ] [Has (Mult D) σ] : {β : Type} → MulTriple D β → Circ σ β
  | _, .get => do
    let a ← rand
    let b ← rand                    -- independent: one round
    let c ← mul a b
    pure (a, b, c)

/-- Squares from random shares. -/
def squareFromRand [Has (Rand D) σ] [Has (Mult D) σ] : {β : Type} → SquarePair D β → Circ σ β
  | _, .get => do
    let r ← rand
    let r2 ← mul r r
    pure (r, r2)
```

Under the offline signature `Lin ⊞ Mult ⊞ Rand` with `rand` free and
`mult` one round, the sketch checks by `rfl` that assembling a triple
costs one round and leaks nothing; its output distribution is that of
`MulTriple.corr`, two fresh draws being one draw from `F²`
(`uniform_prod`). The
last point is the one that matters: a silent handler is hiding, so
replacing `mulTriple` by `tripleFromRand` under any circuit preserves that
circuit's hiding proof (the handler composition theorem of §5).

Two assemblies that *do* open something, and are still hiding because what
they open is independent of everything (both need `Field F`, so they are
described here rather than in the sketch):

```lean
/-- Random bit (odd characteristic): open r², take a square root. -/
def bitFromRand (sqrt : D.F → D.F) : {β : Type} → Bit D β → Circ σ β
  | _, .get => do
    let r ← rand
    let s ← mul r r
    let v ← reveal s                       -- leaks r², uniform on squares, independent of r's sign
    let inv ← const (1 / sqrt v)
    let t ← smul (1 / sqrt v) r           -- ±1
    let one ← const 1
    let u ← add t one
    smul (1/2) u                          -- (±1 + 1)/2 ∈ {0, 1}

/-- Random share with its inverse (Bar-Ilan–Beaver): open r·s for fresh r, s. -/
def randInv : {β : Type} → RandInv D β → Circ σ β
  | _, .get => do
    let r ← rand
    let s ← rand
    let p ← mul r s
    let v ← reveal p                       -- leaks r·s, uniform (given rs ≠ 0), independent of r
    let sInv ← smul (1 / v) s             -- s / (r s) = 1/r
    pure (r, sInv)
```

Their hiding proofs are the Beaver pattern: the simulator draws a fresh
coin and reports it, and the mask lemma says the opened value is that
coin. For `randInv` the map is `s ↦ r·s`, a bijection of the nonzero
elements when `r ≠ 0`: with `randNZ` for both masks the proof is perfect,
with plain `rand` it holds only off `r = 0`, which is exactly the
statistical slack the real protocol has (§8).

**Offline versus online is a cost split, not a semantic one.** Price with a
product resource `(offline rounds, online rounds)`: `Get` costs `(1, 0)`
when assembled, `mult` in the online circuit costs `(0, 1)`. The single
interpreter then reports both counters at once, and "this circuit needs
`n` triples" is the `total` resource on `Get`.

### 6.3 Public coins

A public coin is a correlation whose sample everybody sees. Its model
draws one coin and leaks the *response*, which is why leakage is a
function of request and response:

```lean
def PubCoin.ideal : Model (PubCoin (.ideal F)) F PMF where
  program o := match o with | .coin => uniform F
  leak o x  := match o with | .coin => [x]

/-- A random linear combination of shares, challenge chosen after the shares exist. -/
def randomCombination [Has (Lin D) σ] [Has (PubCoin D) σ] (xs : List D.S) : Circ σ D.S := do
  let r ← coin
  ...                                     -- Σ rⁱ · xᵢ, all linear
```

The distribution of `randomCombination [a, b]` is "draw `r`, reveal
`[r]`", and hiding is immediate: the simulator draws its own coin. This
is the pattern for MAC checks, batched openings and any "challenge" step.

### 6.4 Several coin alphabets

Bits, `Fin n` values (for permutations) and elements of a second ring are
not functions of a uniform field element in odd characteristic, so a
single alphabet of coins would not do. With coins as distributions there
is nothing to do: each feature's ideal model draws from the uniform
distribution on whatever finite type it needs (`uniform F`,
`uniform (Fin (2 ^ m))`, `uniform {x // x ≠ 0}`, `uniform (Fin k → F)`),
and independence across features is `bind`. The leakage alphabet is the
one thing shared across fields, and `Model.mapLeak` with `Encodable`
handles it (§2.9).

### 6.5 Cross-field correlations: edaBits

An edaBit is a random `r < 2^m` shared over the arithmetic field together
with its `m` bits shared over `𝔽₂`. In the field-generic design of §2.9 it
is a capability whose sample spans two fields, and `𝔽₂` is just another
field (`+` is xor, `*` is and), so Boolean circuits are ordinary
`lin`/`mult` circuits over `Bool` (`MultiField.lean`):

```lean
inductive EdaBit (D : Domain) (F : Type) (m : Nat) : Sig where
  | get : EdaBit D F m (D.S F × List (D.S Bool))          -- r, and its m bits (LSB first)

inductive Cap where
  | on (f : Feature) (F : Type) [Concrete F]
  | switch (F G : Type) [Concrete F] [Concrete G]
  | edabit (F : Type) [Concrete F] (m : Nat)

-- ideal model: a uniform r < 2^m, and its bits; nothing leaked
| @Cap.edabit F _ m => ⟨fun | .get => (uniform (Fin (2 ^ m))).map fun r => ((r.val : F), bitsOf m r.val),
                        fun _ _ => []⟩
```

The canonical use is arithmetic-to-binary conversion: reveal `x - r`, then
add the public value back onto the shared bits with a binary adder. The
adder is branch-free (a public bit multiplies, it never `if`s), which is
both the right circuit and what lets evaluation run on symbolic inputs:

```lean
/-- Ripple-carry addition of a public `c` to shared bits: xor free, and one round; `m` rounds. -/
def addPublic [Has (.on .lin Bool) M] [Has (.on .mult Bool) M] :
    List Bool → List (D.S Bool) → D.S Bool → Circ' D M (List (D.S Bool))
  | ci :: cs, ri :: rs, carry => do
    let t ← add ri carry                      -- rᵢ ⊕ carry
    let cb ← const ci
    let s ← add t cb                          -- sᵢ = cᵢ ⊕ rᵢ ⊕ carry
    let rc ← mul ri carry                     -- rᵢ ∧ carry          (the one round)
    let ct ← smul ci t                        -- cᵢ ∧ (rᵢ ⊕ carry)   (public bit: free)
    let carry' ← add rc ct                    -- maj(cᵢ, rᵢ, carry)
    let rest ← addPublic cs rs carry'
    pure (s :: rest)
  | _, _, _ => pure []

/-- A2B: reveal `x - r`, then `x = (x - r) + r` bit by bit. -/
def a2b {F} [Concrete F] (m : Nat) [Has (.edabit F m) M] [Has (.on .lin F) M] [Has (.on .reveal F) M]
    [Has (.on .lin Bool) M] [Has (.on .mult Bool) M] (x : D.S F) : Circ' D M (List (D.S Bool)) := do
  let (r, rbits) ← edabit F m
  let d ← sub x r
  let c ← reveal d                            -- the only revealed value
  let zero ← const false
  addPublic (bitsOf m (Concrete.toNat c)) rbits zero

abbrev mixed : MPC := ⟨[(.on .lin Int, ⟨0,0⟩), (.on .reveal Int, ⟨1,1⟩),
                        (.on .lin Bool, ⟨0,0⟩), (.on .mult Bool, ⟨1,1⟩), (.edabit Int 4, ⟨0,0⟩)]⟩
```

Checked by evaluation (an `Id` model with the mask fixed, `mixed.eval 3`):
the leakage is `[x - 3]` and nothing else (`rfl`), the price is `⟨5, 5⟩`,
one reveal round plus four adder rounds (`decide`), and `a2b 5` yields
`[1, 0, 1, 0]` for two different masks. Hiding is the Beaver pattern with
one coin, perfect when `r` is uniform in the field (`ℤ/2^k` with `m = k`)
and statistical when `r < 2^m` masks a value in a larger field, which is
what a gadget's `ε` (§7) is for. B2A, truncation and comparison via
edaBits are the same ingredients in a different order.

**daBits** (Rotaru–Wood 2019) are the simplest cross-field correlation:
one uniform bit `b`, shared over `F` and over `𝔽₂` (`Cap.dabit F`, ideal
model `(uniform 𝔽₂).map fun b => (b, b)`). Boolean → arithmetic
conversion is one reveal: open `c = x ⊕ b` in `𝔽₂`, then
`x = c + b − 2·c·b` in `F`, linear in `⟦b⟧_F` since `c` is public
(`b2a`). A circuit spanning both worlds, `hammingWeight`, converts each
bit and sums in `F`: all conversions are independent, so one round for
any number of bits (`decide` on the timed model), one revealed bit per
input, and the count comes out as an arithmetic share. Its privacy is
the mask lemma over `𝔽₂`: the revealed `x ⊕ b` is uniform for either
`x`, by the bijection `b ↦ x + b` (`b2a_dist`, `b2a_hiding`), and the
output is `x` in `F` with certainty (`fin_cases` on the two bits).

Switching itself is not special: `Cap.switch F G` is one more priced
capability with an ideal model, exactly like `Cap.on .mult F`, and a
switch implemented via edaBits is a handler for it.

## 7. Gadgets: circuits come with their specs

Clean's `FormalCircuit` bundles a circuit with `Assumptions`, a `Spec` and
the proofs, so that a caller uses the spec and discharges the assumptions
without unfolding the callee. The MPC version (`Gadget.lean`) adds the one
thing MPC cares about: the declared leakage, and the proof that the real
reveals are simulatable from it.

```lean
structure Gadget (M : Model σ L PMF) (I O : Type) where
  circ        : I → Circ σ O
  Assumptions : I → Prop                       -- what the caller must guarantee
  Spec        : I → O → Prop                   -- what the gadget guarantees, under the assumptions
  view        : I → O → List L                 -- declared leakage, of input and output (like `Model.leak`)
  correct     : ∀ i, Assumptions i → ∀ o ∈ (Prod.fst <$> dist M (circ i)).support, Spec i o
  ε           : ENNReal := 0                   -- simulation error, total variation
  simulatable : ∃ Sim : List L → PMF (List L), ∀ i, Assumptions i →
                  PMF.statDist (dist M (circ i))
                    (do let y ← Prod.fst <$> dist M (circ i); let s ← Sim (view i y); pure (y, s)) ≤ ε

def Gadget.cost   (g) (K : CostModel σ C) (i : I) : PMF C   -- computed, per MPC; a point for structural circuits
def Gadget.Priced (g) (K) (p : C) : Prop := ∀ i, g.cost K i = pure p

/-- Inversion by masking: needs x ≠ 0; the mask is a random nonzero share, so correctness is
perfect and the one revealed value is a uniform nonzero element. -/
def invertGadget : Gadget (InvSig.ideal F) F F where
  circ := invert                    -- s ← randNZ; v ← mul x s; m ← reveal v; smul m⁻¹ s
  Assumptions x := x ≠ 0
  Spec x y := y * x = 1
  view _ _ := []
  correct := …                      -- every output is x⁻¹: field algebra on the support
  simulatable := Gadget.perfect …   -- simulator: a fresh uniform nonzero element; `Equiv.mulLeft₀`

theorem invert_priced : (invertGadget F).Priced (InvSig.comm F) 3        -- one mult, one reveal
example : delayOn (InvSig.timed F 0) (invert ⟨x, 0⟩) = 2 := rfl         -- random shares free
example : delayOn (InvSig.timed F 1) (invert ⟨x, 0⟩) = 3 := rfl         -- random shares cost a round
```

Three choices are visible here (decisions 009, 011):

* **Correctness is perfect.** Every output the circuit can produce
  satisfies the spec: a statement on the support of the output
  distribution, which for a coin-free circuit is `rfl`. There is no set
  of "good coins". A gadget that needs an invertible mask asks the
  functionality for one (`randNZ`, a uniformly random nonzero share, a
  priced feature like any other) rather than gambling on the coins.
* **The error is in privacy, as a number.** `ε` is total variation
  between the real and the simulated (output, reveals); perfect gadgets
  carry `0` and prove an equation (`Gadget.perfect`). This is what adds
  under composition, and it is where the statistical masking of §6.5
  will live.
* **No price.** A circuit has semantics regardless of the MPC, but a
  cost only once an MPC is fixed: its `output` and `leak` are determined
  by the `program` and `leak` of the functionalities it calls, the same
  everywhere; its delay and communication need that MPC's latencies and
  bandwidths. So `Gadget.cost` takes the MPC's cost model as an argument,
  and a bound is a separate theorem about the pair: the same
  `invertGadget` has delay 2 or 3 depending on the MPC (decision 005).

**Composition** is by specification. A gadget is one operation of a
one-op signature (`Gadget.toModel`: `program := its output distribution`,
`leak := view`) realised by its circuit (`Gadget.impl`,
`Gadget.realizes`); callers are written in the hybrid where that
operation is primitive, and `handle_realizes` (§4.1) transports their
proofs. The caller's obligation is exactly Clean's: discharge the
gadget's assumptions at the call site. Sequential composition of two
gadgets is the two-call caller `do o ← call g₁ i; call g₂ o`, so no
`Gadget.seq` primitive is needed, and its view is the two records, which
is the only thing a composite could honestly declare (the intermediate
output is a hidden, possibly random handle, so a composite's view cannot
be a function of its own input and output alone).

A gadget's `Assumptions` and `view` are its interface; a capability class
(§2.5) whose instances are gadgets with a common spec gives the "same
interface, several implementations, prices differ" pattern for free.

## 8. Extensions, in the order they will be needed

1. **Statistical composition.** `ε` exists on gadgets and on
   realisations (`RealizesStat`); what is missing is the lemma that makes
   it add: `bind` is a contraction in total variation (data-processing),
   so `handle_realizes` holds up to the sum of the per-call errors.
   Needed for edaBit masking of a bounded value by a longer one (§6.5).
2. **Adaptive environment.** Party inputs that depend on earlier openings:
   make `Model.program` a function of the leakage so far.
3. **Corruption.** Tag leaked values with recipients (`revealto p`), view
   includes corrupt parties' inputs; both are instances of `view`.
4. **Abort / malicious.** An `Abort` response in the signature (`Option`
   results); hiding then also quantifies over adversarial abort choices.
5. **Static round bounds.** A syntactic `Circ.bound` that over-approximates
   `cost` without running, for circuits with data-dependent control flow.

## 9. Proof methodology, summarised

| Property           | Concrete circuit                      | Generic circuit                         |
|--------------------|---------------------------------------|-----------------------------------------|
| correctness        | `rfl` / `decide` / `ring`; on the support for coins | `simp [run_bind, …]` + algebra   |
| delay / cost       | `rfl`                                 | `simp [run_bind]` + `omega`             |
| hiding (coin-free) | `Hiding.of_lift`, `rfl`               | `hiding_of_silent`; realisations        |
| hiding (coins)     | `simp` unfolds the run; `uniform_map_equiv` with an `Equiv` | `handle_realizes`, `Hiding.transport` |
| not hiding         | two inputs, evaluate (`leakyMul_not_hiding`) | —                                |

Evaluation means `rfl` or kernel `decide`; `native_decide` is not used.

## 10. Names

Clean is the sibling, so a one-word English word that puns on Lean, or
rhymes with it, or says what MPC does.

* **Glean** — "to glean": gather scraps of information. The adversary
  gleans only what the circuit opens; the framework is about bounding that.
  Same shape as Clean. My first choice.
* **Convene** — parties convene to compute; rhymes with Clean.
* **Unseen** — hiding; rhymes with Clean.
* **Screen** — screens values from view; also a stage on which things run.
* **Oblean** — oblivious + Lean.
* **Veil** — hiding, short, not a Lean pun.
* **Between** — a secret is split between parties.
* **Seal**, **Shroud**, **Curtain** — hiding metaphors, no Lean pun.

Avoid *Shamir*, *Beaver*, *SPDZ*-derived names: the framework is
explicitly protocol-agnostic.

## 11. Reveal questions

* **`Type 1`.** Quantifying over response types puts `Circ σ α` in
  `Type 1`. Harmless so far; if it bites (universe issues in Mathlib
  interop), index requests by a code for the response type instead.
* **Parallelism is computed.** `bind` never parallelises, and there is no
  parallel node; the timed domain reads the dependency graph (decision
  002). A circuit whose branch on a revealed value is not a data
  dependency must say `barrier`; forgetting it under-counts, which a
  syntactic check ("every `if` on a revealed value is preceded by a
  barrier") could enforce.
* **Mathlib is the base.** The sketch depends on Mathlib and uses its
  definitions wherever one exists: `Field`, `CommRing`, `Inv` and `ZMod`
  for fields (`ring`/`field_simp` close the algebra), `Encodable` for the
  shared leak alphabet, `Equiv` for the mask lemma, `PMF` and
  `uniformOfFintype` for the semantics, `AddMonoid` for costs, `WithTop`
  for unbounded cost, `Fin m →` vectors. See
  `decisions/010-mathlib.md`.
* **Coin alphabet.** None to choose: each feature draws from the uniform
  distribution on the finite type it needs, and independence across
  draws is `bind` (§6.4).
* **Evaluation scales like evaluation.** Closing theorems by `rfl` runs
  the interpreter inside `whnf`; around a dozen sequential rounds it takes
  tens of seconds, and kernel `decide` needs a closed instance. Both are
  fine for examples and for concrete small circuits. Real proofs go
  through the compositional lemmas (§5), which never evaluate the circuit,
  and through gadget specs (§7), which never unfold callees.
* **Equality of circuits.** Do we want an equational theory (independent
  calls commute up to cost/leak-equivalence) or only observational
  equivalence via `run`? Observational is enough for everything above.
