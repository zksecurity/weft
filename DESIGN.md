# Verifying MPC programs in Lean 4 — design notes

Name: **Weft** (see §10 for how it was chosen). The reasons behind each
choice, with the alternatives rejected, are in `decisions/`, one record
per decision; this document describes the design as it stands. The
revision of 2026-09-05 (structural events, hybrids as lists, one
certificate) is recorded authoritatively in `report.md`, section "Final
design"; the two decision records it adds are `decisions/014` ("Public
observations are explicit and never automatic") and `decisions/015` ("One
certificate: realisation of an explicit functionality").
Companion files, under `Weft/` (the library builds; no theorem is
`sorry`, and §4.1 lists what is described but not yet stated in Lean):
`Shape.lean` (domains, response shapes, operands), `Interface.lean`
(interfaces, requests, events), `Prog.lean` (the free monad of programs),
`Model.lean` (models, the interpreter and its laws), `Timed.lean` (delay
by dependency tracking), `Functionality.lean` (functionalities, hybrids as
lists, `Has`), `PMF.lean` (the mask lemma, joint uniformity, total
variation), `Std/Arith.lean` and `Std/Random.lean` (the standard
functionalities), `Std/Hybrids.lean` (`Std`, `Pre`), `Realization.lean`
(the one certificate and its composition theorem), `Cost.lean` (price
lists; composition for communication), `Statistical.lean` (statistical
realisations and the kernel lemma) and `Program.lean` (the `program`
command). Under `Examples/`: `Basic.lean` and `Gallery.lean` (programs in
different styles, with their theorems closed by evaluation),
`Beaver.lean` (multiplication from triples: why the masks must be jointly
uniform, with a counterexample), `Privacy.lean` (the certificate and what
it composes to), `Inversion.lean` (preconditions), `AesHybrid.lean` (from
the AES-hybrid to a plain program, end to end), `MultiField.lean` (generic
over field types, switching, edaBits, daBits), `Timing.lean` (delay, and
how a cost model instantiates an abstract operation), `RandomCombination.lean`, `Silent.lean`,
`Statistical.lean` and `Checked.lean` (what `program` rejects). The
library depends on Mathlib.

## 1. What we are verifying, and what we are not

An *MPC program* here is a program that drives an ideal functionality
(an "arithmetic black box"): it hands the functionality shared values,
asks it to multiply, open, compare, and so on, and does ordinary
computation on whatever comes back in the clear. When it is straight-line
we also call it a circuit; a program that implements one functionality
over others is a protocol.

We deliberately do **not** model the MPC protocol: no shares, no parties'
views, no network. The functionality is a black box whose behaviour is a
Lean definition. Three consequences shape everything below:

* **No witness, no soundness/completeness split.** A ZK circuit is a
  relation checked against a prover-supplied witness; an MPC program is a
  function of its inputs and of the coins the functionality hands out
  (`rand`, Beaver triples). The properties of interest are *functional
  correctness*, *cost* and *privacy*.
* **Interaction is the program.** Opening a value, computing on it in the
  clear and inserting the result back is not a special case; it is the
  basic shape of a program. So the program language is a monad whose
  effects are requests to the functionality, and the "reactive
  functionality" is just the interpreter of that monad.
* **Privacy is a property of the program, not of the protocol.** Because
  the functionality is ideal, the adversary's entire view is the *tagged
  trace*: one event per request, recording which operation was invoked
  (the program is public, so this includes the operation's clear
  arguments), the clear part of the response, and whatever disclosure the
  functionality declares (§4.1, decision 012). "Reveals nothing beyond its
  specification" becomes: *the program realises a functionality*, i.e.
  the joint distribution of (response, trace) is the functionality's
  response paired with the output of a simulator that is handed the
  functionality's own event and nothing else. For coin-free programs the
  distribution is a point, the simulator replays a fixed list, and the
  statement is checked by evaluation; with coins it is an equation between
  distributions, proved by unfolding the run and one lemma: a uniform mask
  pushed through a bijection is uniform.

### Cues from Clean, and what does not carry over

Clean (the Lean 4 ZK framework) gets several things right that we copy:

| Clean                                             | Here                                                              |
|---------------------------------------------------|-------------------------------------------------------------------|
| Circuit is a monadic DSL; the monad records ops   | Same: `Prog ι D` is a free monad over an interface `ι`            |
| `ProvableType` maps structured Lean types to vars | `Domain` with an abstract share constructor `D.sh`; response `Shape`s (§2.1, §3.3) |
| `FormalCircuit` bundles circuit + assumptions + spec + proofs | `Realization` bundles implementation + precondition + simulator + equation; the spec is a functionality (§7) |
| Subcircuits with local proofs compose             | Realisations compose (`Realization.comp`); cost and privacy lemmas are compositional (§5) |

What does not apply: witness generation, constraints and their soundness,
lookups and table layout, the completeness/soundness pair, `Environment`
as an assignment of witness cells. There is no "elaborated circuit" as a
constraint system; the program *is* its own semantics.

## 2. Core model

### 2.1 Interfaces: what a functionality offers

An interface is a *vocabulary*: the public operations, the shapes of the
operands of each, and the shape of its response. A request is an
operation applied to operands; a clear operand (a constant, a scalar, an
opened value) has a clear shape, a secret input is a share, so the
public part of a request is structural (`Interface.lean`, `Shape.lean`):

```lean
structure Domain where sh : Type → Type              -- what a share of a `T` is
abbrev Domain.ideal  : Domain := ⟨fun T => T⟩         -- a share is its value: semantics and privacy live here
abbrev Domain.erased : Domain := ⟨fun _ => Unit⟩      -- what the adversary sees of a response

inductive Shape | unit | clear (T : Type) | share (T : Type) | prod (a b : Shape) | vec (n : Nat) (a : Shape) | list (a : Shape)
def Shape.interp (D : Domain) : Shape → Type          -- `share T ↦ D.sh T`, `clear T ↦ T`, …
def Shape.blank : (s : Shape) → s.interp D → s.interp .erased   -- clear parts kept, shares become `()`

structure Interface where
  Op   : Type                                         -- operations
  dom  : Op → List Shape                              -- operand shapes: `clear F` public, `share F` secret
  cod  : Op → Shape                                   -- response shape
  leak : Op → Type := fun _ => Unit                   -- type of the declared disclosure

def Operands (D : Domain) : List Shape → Type        -- a value of each operand shape
structure Req (ι : Interface) (D : Domain) where (op : ι.Op) (args : Operands D (ι.dom op))
abbrev Resp (ι : Interface) (D : Domain) (o : ι.Op) : Type := (ι.cod o).interp D
structure Event (ι : Interface) where
  (op : ι.Op) (args : Operands .erased (ι.dom op)) (out : Resp ι .erased op) (leak : ι.leak op)
```

An `Event` is the adversary's record of one request: the operation, the
clear part of the operands, the clear part of the response, the declared
disclosure. The first three are structural, computed by the interpreter
from the shapes; only the last is written by the functionality's author
(decision 014).

A *functionality* is an interface with its meaning (§2.10, §3.1). The
standard ones live in `Std/`; each is an inductive of operations, an
interface, and a model:

```lean
namespace Lin
inductive Op | const | add | sub | smul
abbrev ops (F : Type) : Interface where
  Op := Op
  dom | .const => [.clear F] | .add => [.share F, .share F] | .sub => [.share F, .share F] | .smul => [.clear F, .share F]
  cod _ := .share F
end Lin
abbrev Lin (F : Type) [Add F] [Mul F] [Sub F] : Functionality := .ofEval (Lin.ops F) (Lin.eval F)

abbrev Mult      (F) : Functionality      -- mult   : [share F, share F] → share F ; always silent
abbrev Reveal    (F) : Functionality      -- reveal : [share F] → clear F ; the response is public by shape
abbrev Cmp       (F) : Functionality      -- lt     : [share F, share F] → share F
abbrev Rand      (F) : Functionality      -- rand   : [] → share F, uniform            (Std/Random.lean)
abbrev PubCoin   (F) : Functionality      -- coin   : [] → clear F, uniform: public by shape
abbrev MulTriple (F) : Functionality      -- get    : [] → share F × share F × share F, (a, b, a·b)
abbrev Barrier       : Functionality      -- barrier : [] → unit; its own timed model (§3.5)

abbrev Hybrid := List Functionality
abbrev Std (F) : Hybrid := [Lin F, Mult F, Reveal F]          -- the arithmetic black box
abbrev Pre (F) : Hybrid := [Lin F, Reveal F, MulTriple F]     -- the preprocessing model

class Has (F : Functionality) (fs : Hybrid) where (i : Fin fs.length) (eq : fs.get i = F)   -- the certificate
```

A *hybrid* is a list of functionalities, available as black boxes. Its
interface indexes the list (`fs.ops.Op := (i : Fin fs.length) × (fs.get
i).ops.Op`), and `Has F fs` is a position and one equality of
functionalities, from which operands, response, program and disclosure
all transport (`Prog.op` transports a request along `eq`; on a literal
list the equality is `rfl` and everything computes). The instances
`Has.here` and `Has.there` walk a literal list, so a program written
against `[Has (Lin F) fs] [Has (Mult F) fs]` runs on *every* hybrid that
lists those two functionalities, in any order and with anything else
alongside. This is the "different subsets of features" requirement,
solved by the usual data-types-à-la-carte instances on a list rather than
on a sum of signatures.

Randomness is a *feature of the functionality*, not of the program
language: `rand`, `coin` and `mulTriple` are requests like any other.
Which of them an MPC offers, and what they cost, is again a list (§2.6).

### 2.2 Programs: the free monad

```lean
inductive Prog (ι : Interface) (D : Domain) : Type → Type where
  | pure : α → Prog ι D α
  | call (r : Req ι D) : (Resp ι D r.op → Prog ι D α) → Prog ι D α      -- ask, then continue
```

`call r k` sends request `r` and continues with `k` on the response.
The continuation is arbitrary Lean code: that is where the "compute in the
clear and insert back" happens, with no special support, and where a
program branches on a public value.

```lean
def divByOpened [Has (Lin F) fs] [Has (Reveal F) fs] [Div F] [OfNat F 1] (x d : D.sh F) : Prog fs.ops D (D.sh F) := do
  let dv ← reveal d           -- functionality → environment
  smul (1 / dv) x            -- clear arithmetic, then environment → functionality
```

There is no parallel node. Monadic `bind` is sequential *as a program*, but
delay is not read off the program order: it is computed from data
dependencies in the timed domain (§3.5), so `mapM mul` over a list is one
round and a product tree written with plain binds costs its depth. The
only annotation a program ever needs is a `barrier` where it branches on a
revealed value (decision 002).

`Prog ι D` is a lawful monad (`bind_pure`, `bind_assoc` by induction), so
`do`-notation, `List.mapM`, etc. all work, and the interpreter and every
compositional theorem have exactly two cases. `Prog.handle` implements
every request of one interface by a program over another; it is inlining,
and it is what composition means (§5).

### 2.3 Why programs cannot cheat

Programs are polymorphic in the domain `D`. Since `D.sh T` is an abstract
type, the only functions from `D.sh T` to anything are the ones the
interface offers. A program cannot look at a share; it can only ask the
functionality to open it, and opening is exactly what the trace records.
Lean's typing enforces this for a computable `def`: comparing two shares
would need a `DecidableEq (D.sh T)` instance that does not exist, and
supplying one classically makes the definition noncomputable. What typing
does not catch (`noncomputable`, `unsafe`, `implemented_by`, `partial`, or
a parameter of the certificate that hands in a way to inspect shares) the
`program` command checks on the fully applied implementation (§7,
`Examples/Checked.lean`). The privacy theorems themselves are about the
program instantiated at the ideal domain, where a share is its value, and
are proved by evaluation.

### 2.4 What a program looks like

A user writes against the functionalities they need and nothing else.
Here is the whole of a one-round "dot product plus constant" and of Horner
evaluation (`Examples/Basic.lean`):

```lean
/-- ⟨xs, ys⟩ + c.  One round: the products in parallel, then free linear operations. -/
def dotPlus [Has (Lin F) fs] [Has (Mult F) fs] [OfNat F 0] (xs ys : List (D.sh F)) (c : F) :
    Prog fs.ops D (D.sh F) := do
  let ps ← (xs.zip ys).mapM fun p => mul p.1 p.2
  let s ← sumAll ps
  let k ← const c
  add s k

/-- Σ aᵢ xⁱ by Horner: each multiplication depends on the last, so n rounds. -/
def horner [Has (Lin F) fs] [Has (Mult F) fs] [OfNat F 0] (x : D.sh F) : List (D.sh F) → Prog fs.ops D (D.sh F)
  | [] => const 0
  | a :: as => do
    let r ← horner x as
    let t ← mul r x
    add t a
```

Things to notice:

* `D.sh F` is opaque, so `mul`, `add`, `const` are the only things that can
  happen to a share; `c : F` is a clear value the environment supplies,
  and it travels in the operation (`Lin.Op.const c`), where the adversary
  sees it.
* Parallelism is where you wrote it: the `mapM` gives one round, the
  recursion in `horner` gives `n`. The framework does not reschedule.
* Nothing says which MPC this runs on. Instantiating `fs := Std F` runs it
  on the arithmetic black box; `fs := Pre F` (after the Beaver
  realisation, §5) runs it on a preprocessing functionality; the theorems
  below are stated once and hold for both.

And what the user proves, all by `rfl` for concrete sizes:

```lean
example : output (Std F).eval (dotPlus (fs := Std F) (D := .ideal) [a, b] [c, c] k) = a * c + b * c + k := rfl
example : delayOn (Std.timed F) (dotPlus (fs := Std F) (D := .timed) [⟪a⟫, ⟪b⟫] [⟪a⟫, ⟪b⟫] k) = 1 := rfl  -- §3.5
example : delayOn (Std.timed F) (horner (fs := Std F) (D := .timed) ⟪x⟫ [⟪a₀⟫, ⟪a₁⟫, ⟪a₂⟫]) = 3 := rfl
example : view (Std F).eval (horner (fs := Std F) (D := .ideal) x [a₀, a₁, a₂])
    = [⟨Std.lin F (.const 0), (), ()⟩, ⟨Std.mult F, (), ()⟩, ⟨Std.lin F .add, (), ()⟩, …] := rfl   -- silent records only
```

### 2.5 Polymorphism over the hybrid

`[Has F fs]` makes a program *run* on every hybrid that lists `F`. A
program whose *implementation* should depend on what is available (an AES
S-box that uses native inversion when the MPC offers it and `x^254`
otherwise) is written against a **capability class**, whose instances are
the strategies (`Examples/Gallery.lean`):

```lean
abbrev Inversion (F : Type) [Inv F] : Functionality                 -- native inversion: inv : [F] → share F

class HasInv (F : Type) (fs : Hybrid) (D : Domain) where            -- "some way to invert"
  inv : D.sh F → Prog fs.ops D (D.sh F)

instance (priority := high) [Inv F] [Has (Inversion F) fs] : HasInv F fs D := ⟨fun x => nativeInv x⟩
instance [OfNat F 1] [Has (Lin F) fs] [Has (Mult F) fs] : HasInv F fs D := ⟨fun x => expPublic x 254⟩

def sbox [HasInv F fs D] (affine : D.sh F → Prog fs.ops D (D.sh F)) (x : D.sh F) : Prog fs.ops D (D.sh F) := do
  let y ← HasInv.inv x
  affine y
```

Instance priority picks the native functionality when the hybrid lists it
and falls back otherwise. The S-box source is written once; on `Std` it
costs 13 rounds, on `[Lin F, Mult F, Reveal F, Inversion F]` one round,
both by evaluation. Correctness is proved per instance against the same
functionality (`output = x⁻¹` then affine), so a capability class carries
a *specification* the way a realisation does (§7): every strategy must
realise it, and a caller's proof uses only the specification. This is the
MPC analogue of Clean's subcircuits with local proofs, with the extra
twist that which subcircuit you get is decided by the type class.

The same mechanism, one level up, handles whole functionalities: an AES
*functionality* offered natively by some MPC (`AES F aes`, one operation,
opaque) versus an AES *program* over `Std`. A protocol written against
`[Has (AES F aes) fs]` runs on either (§2.10, `Examples/AesHybrid.lean`).

### 2.6 The MPC as one value: a price list

Should the set of enabled functionalities be part of the program's type,
with subtyping to require one? Yes, and there should be exactly one thing
that describes an MPC. The design that satisfies both (`Cost.lean`,
decision 003):

**An MPC is a hybrid instantiated in the cost model.** A functionality
is behaviour only; it has no cost (decision 017). An MPC is a list of
functionalities, each *instantiated*: paired with a model of its
interface in the scheduling monad, which does the behaviour and pays
the price. A functionality that is absent is not offered, which is the
same as infinitely expensive. Everything else is derived from that one
value:

```lean
structure Price where (delay : Nat) (comm : Nat)                  -- rounds and communication, per operation

abbrev MPC.Entry := (F : Functionality) × Model F.ops .timed Sched  -- a functionality, instantiated
abbrev MPC := List MPC.Entry

def MPC.hybrid   (M : MPC) : Hybrid                              -- the functionalities, in order
def MPC.timed    (M : MPC) : Model M.hybrid.ops .timed Sched     -- the cost instantiation: dispatch by position
abbrev MPC.model (M : MPC) := M.hybrid.model                     -- the semantics: never the MPC's to choose

abbrev abb : MPC := [(Lin F).priced ⟨0, 0⟩, (Mult F).priced ⟨1, 2⟩, (Reveal F).priced ⟨1, 1⟩]
-- `F.priced p := ⟨F, Model.timed F.eval fun _ => p⟩`: the generic timed model of `F`'s interface at price `p`;
-- `MPC.entry F T` takes any timed model of `F.ops`; `MPC.derived M f` runs a realisation (§3.4)
```

* **The type carries the feature set.** A program over `M.hybrid.ops` may
  only use what `M` lists: a request names a position, and `Prog.op`
  needs `Has F M.hybrid` for the functionality it calls. Calling
  `nativeInv` against an MPC without `Inversion F` is a failed instance
  search at the call site, not a runtime `⊤`.
* **Offered means instantiated, by construction.** `M.timed` is total on
  the hybrid's operations, since every operation of the hybrid names the
  entry it belongs to. There is no `⊤` and no `Option`: the cost of
  something the type system has ruled out is never asked for.
* **Subtyping is `Incl fs gs`** (every component of `fs` is available in
  `gs`), and `Prog.weaken` coerces `Prog fs.ops D α` to
  `Prog gs.ops D α`. It is a handler, so it costs nothing and changes
  nothing semantically.
* **Semantics is per functionality, once.** The hybrid's model dispatches
  by position to the component's own ideal model; `M.model` is assembled
  from the entries with no per-MPC code. An MPC only instantiates, it
  never redefines what an operation means: its timed models compute the
  same values as `eval`, and the ideal semantics does not mention them.
  Two MPCs that both list `Mult F` agree on what `mult` computes and
  discloses, and differ only in rounds and bytes.

The capability-class pattern of §2.5 is unchanged: the instances are
`[Has (Inversion F) fs]` (native) and `[Has (Lin F) fs] [Has (Mult F) fs]`
(fallback).

A price is per *operation*, never per value: a timed model sees the
request, that is the operation and the operands with their ready times,
so a hand-written model may price `const` per coefficient if an MPC
wants to (report, Issue 4), or charge a compound operation per input (a
timing profile, §3.4); but the price of a request never depends on what
a share holds.

**An open world.** A functionality is a value, not a constructor of a
library-owned enumeration, so a downstream user adds one by defining it,
and `Has` finds it in any list that mentions it. What is given up is
exhaustiveness: nothing can enumerate "all functionalities", and two
entries that are the same functionality at different positions are two
entries (the duplicate-entry and reindexing policy for lists is recorded
as open in the report).

### 2.7 Adding functionalities later must not break anything

The user-visible contract is: a program that did not use a functionality
is unaffected by that functionality being added, to the library or to an
MPC. Three disciplines guarantee it:

1. **Programs state lower bounds, never a set.** A program is
   `{fs : Hybrid} [Has (Lin F) fs] [Has (Mult F) fs] … : Prog fs.ops D α`.
   It is generic in `fs`; only examples and top-level deployments pin a
   list. A longer list still satisfies the bounds.
2. **Hybrids are lists, and absence is the default.** Adding a
   functionality to the library is defining a value; no existing list
   changes. Adding one to an MPC appends an entry; every `Has` that held
   before still holds (`Has.there`), and `Prog.weaken` with the `Incl`
   instance is the coercion.
3. **Per-functionality semantics travel with the value.** A functionality
   carries its own evaluation model, ideal model and timed model, so the
   hybrid's model needs no case per name, and there is no library-owned
   total function to extend.

What survives unchanged: every program, every theorem about it stated with
price hypotheses (§4.2) or against a named MPC value, and every
`Realization` (§7), whose hybrid is exactly its list of `Has` bounds.

### 2.8 Programs over a field

The algebra of the clear type is a property of the field `F`, not a
feature of the MPC. A program that needs it says so with a class
constraint next to its `Has` bounds; with Mathlib that is `Field F`
(`Examples/Inversion.lean`):

```lean
/-- Inversion by masking: `1/x = s / open(x·s)`.  Division in the clear, and coins. -/
def invert [Has (Lin F) fs] [Has (Mult F) fs] [Has (Reveal F) fs] [Has (RandNZ F) fs] (x : D.sh F) :
    Prog fs.ops D (D.sh F) := do
  let s ← randNZ F
  let v ← mul x s
  let m ← reveal v
  smul m⁻¹ s
```

Lagrange interpolation at a public point is the other canonical example:
the coefficients need division and are computed in the clear, the
combination is linear, so it is zero rounds, and `Field F` with
`[Has (Lin F) fs]` is all it asks for.

Three things follow. A ring-only MPC (`ℤ/2^k`) has a clear type that does
not satisfy `Field`, so `invert` does not elaborate against it, while a
program asking only for `CommRing F` runs on both. Correctness proofs of
field programs are field algebra (`field_simp`, `ring`) on the output,
for every value of the mask, e.g. `(x·s)⁻¹·s = x⁻¹` for `invert` with
`s ≠ 0` (`invert_correct`). The mask comes from `RandNZ`, a random
*nonzero* share the functionality guarantees, so `invert` is perfectly
correct and, for `x ≠ 0`, perfectly private: the opened `x·s` is a uniform
nonzero element (`invertReal`, §7). With a plain `rand` the same program
would be correct and private only off `s = 0`; that is where statistical
error (§8) would enter, and the design keeps it out by asking the
functionality for what the proof needs (decision 011).

### 2.9 Several fields: generic over the field, switching as a functionality

Fields are not named or numbered. Shares are a type constructor, `D.sh F`
is "a share of an `F`", every functionality is instantiated at a field
type, the field's algebra is a typeclass on `F`, and switching is one more
functionality over two field *types* (`Examples/MultiField.lean`,
decision 004):

```lean
abbrev Switch (F G : Type) [Encodable F] [NatCast G] : Functionality   -- switch : [F] → share G
abbrev EdaBit (F : Type) [NatCast F] (m : Nat) : Functionality         -- get : [] → share F × vec m (share GF2)
abbrev DaBit  (F : Type) [NatCast F] : Functionality                   -- get : [] → share F × share GF2

def mul    [Mul F] [Has (Mult F) fs] (a b : D.sh F) : Prog fs.ops D (D.sh F)
def rand   (F) [Fintype F] [Inhabited F] [Has (Rand F) fs] : Prog fs.ops D (D.sh F)    -- nothing fixes the field: pass it
def switch (G) [Encodable F] [NatCast G] [Has (Switch F G) fs] (a : D.sh F) : Prog fs.ops D (D.sh G)
```

A program is generic over the fields it touches; `let a ← switch G b`
elaborates only if the hybrid lists the switch from `b`'s field to `G`:

```lean
def mulThenCompare (F G : Type) [CommRing F] [Encodable F] [CommRing G] [Encodable G] [LT G] [DecidableRel …]
    [Has (Mult F) fs] [Has (Switch F G) fs] [Has (Cmp G) fs] [Has (Switch G F) fs]
    (a b c : D.sh F) : Prog fs.ops D (D.sh F) := do
  let ab ← mul a b                              -- in F
  let ab' ← switch G ab                         -- both conversions independent: one round
  let c' ← switch G c
  let bit ← lt ab' c'                           -- comparison is offered on G
  switch F bit                                  -- back in F

abbrev twoField : MPC := [(Mult (ZMod 7)).priced ⟨1, 2⟩, (Cmp (ZMod 16)).priced ⟨2, 6⟩,
                          (Switch (ZMod 7) (ZMod 16)).priced ⟨3, 8⟩, (Switch (ZMod 16) (ZMod 7)).priced ⟨2, 4⟩, …]
-- instantiates at F := ZMod 7, G := ZMod 16; output, cost and delay by evaluation
```

Which field a value lives in is in its type, so an operation infers its
field from its argument and a mismatch is a type error. The MPC prices
per (functionality, field): multiplication on two fields are separate
entries, and each direction of a switch has its own price.

Three consequences of "the field is the type":

* **Semantics is assembled from the entries.** Each entry is a
  functionality carrying its own model, so `M.model` works for every `M`
  with no per-MPC code. A switch's ideal model is whatever conversion the
  protocol guarantees (the canonical representative re-read in the
  target, bit decomposition, embedding into an extension), stated once
  per pair of field types.
* **The cost sits where `Has` looks.** `Has` gives a position and
  `MPC.timed` dispatches to the entry at that position, so the cost model
  needs no decidable equality on types and no `⊤`: every well-typed
  program has a finite, total cost on its MPC.
* **Universe.** `Shape`, `Interface` and `Functionality` mention `Type`
  and live in `Type 1`; programs `Prog ι D α` live in `Type`, and nothing
  so far has needed more.

Each event carries its clear outputs at their own type (`Event.out :
Resp ι .erased op`) and its disclosure at the type the operation declares,
so there is no shared leakage alphabet to encode into; `Encodable` is used
only where a conversion needs a canonical representative. Coins need no
conversion either: each field's model draws from the uniform distribution
on that field (§6.4). This covers arithmetic/Boolean mixing (daBits become
a correlation across two fields), `ℤ/2^k ↔ 𝔽_p` switching, and
extension-field MAC checks.

### 2.10 One notion: functionalities and realisations

There is no distinction in kind between the MPC's multiplication and an
AES program. Both are **functionalities**: an interface with its meaning,
one joint step per request. What differs is how they come to exist
(`Functionality.lean`, `Realization.lean`, decision 006):

```lean
structure Functionality where
  ops   : Interface
  eval  : Model ops .ideal Id                      -- coins fixed to a dummy: evaluation by `rfl`
  IsModel : Model ops .ideal PMF → Prop            -- the semantics, as the predicate it uniquely satisfies
  isModel_unique : ∃! M, IsModel M                 -- and nothing about cost (decision 017)

noncomputable def Functionality.model (F : Functionality) : Model F.ops .ideal PMF   -- the unique such model

/-- `F` is realised over the hybrid `fs`: a program for every operation and every domain, a simulator
that sees only `F`'s event, and the equation, on requests satisfying `Pre`. -/
structure Realization (F : Functionality) (fs : Hybrid) where
  impl : (D : Domain) → (r : Req F.ops D) → Prog fs.ops D (Resp F.ops D r.op)
  Pre  : Req F.ops .ideal → Prop := fun _ => True
  Sim  : Event F.ops → PMF (List (Event fs.ops))
  real : ∀ r, Pre r → dist fs.model (impl .ideal r) =
           do let (y, d) ← F.model.step r; let s ← Sim ⟨r.op, (F.ops.cod r.op).blank y, d⟩; pure (y, s)

def Realization.incl (F) (gs) [Has F gs] : Realization F gs                        -- trusted: calling `F` realises `F`
def Realization.comp : Realization F fs → Realizations fs gs → Realization F gs    -- inlining; `real` composes
```

The semantics of a functionality is a `PMF` model, and `PMF` is not
computable; it is stored as the predicate `IsModel` it uniquely satisfies
so that a functionality *value* is computable, since a program over a
literal hybrid mentions its functionalities. An author writes
`IsModel := (· = M)` for the model they mean and states `F.model = M` once
(`Functionality.model_eq`); deterministic functionalities are
`Functionality.ofEval`, whose semantics is the evaluation model lifted.

Functionalities and realisations form a category, up to the
preconditions: objects are functionalities, morphisms are "implemented
over", identities are trust (`Realization.incl`), and composition is
inlining, with the equation composing by the theorem of §4.1. Everything
earlier is an instance:

| Earlier notion                 | As a functionality / realisation                                   |
|--------------------------------|--------------------------------------------------------------------|
| primitive operation (`mult`, `rand`, `reveal`) | a functionality the MPC provides; realisation `incl`; price on the MPC's list |
| MPC price list (§2.6)          | the list of functionalities realised by `incl`, each instantiated in the cost model |
| `Has F fs`                     | the trivial realisation `Realization.incl F fs`                    |
| program with spec and declared disclosure | a one-operation functionality realised over `fs` (§7)  |
| gadget (old §7)                | such a realisation plus a `Pre`; a price is a separate theorem per MPC |
| handler (`beaver`, "`Std` on `Pre`") | `Realizations (Std F) (Pre F)`: Beaver for `Mult`, `incl` for the rest |
| capability class (§2.5)        | several realisations of one functionality; instance choice picks one |
| derived price                  | the cost of `impl` on the target; composes through `comp` as prices do (`cost_handle`) |

The AES example says it concretely (`Examples/AesHybrid.lean`). `AES F
aes` is a functionality with one operation, program `aes k m`, nothing
declared. `cbc2` is written against `[Has (AES F aes) fs] [Has (Lin F)
fs]` and knows nothing about how AES exists. Instantiation one: the MPC
offers AES natively, `Realization.incl`. Instantiation two:
`aesByProgram`, a program over the black box with one new obligation, its
own `real` proof. Either way the protocol's own specification `CBC` is
realised once, in the AES-hybrid, and composition moves it to whichever
realisation is plugged in:

```lean
program cbcOverHybrid : Realization (CBC F) (AesHybrid F) where      -- once, against the AES specification
  impl D r := cbc2 toyAes r.args.1 r.args.2.1 r.args.2.2.1 r.args.2.2.2.1
  Sim _ := pure [⟨⟨1, .add⟩, (), ()⟩, ⟨⟨0, .enc⟩, (), ()⟩, ⟨⟨1, .add⟩, (), ()⟩, ⟨⟨0, .enc⟩, (), ()⟩]
  real r _ := by …

noncomputable def hybridOverStd : Realizations (AesHybrid F) (Std F) :=
  .cons (aesByProgram F) (Realizations.incl [Lin F, Mult F, Reveal F] (Std F))
noncomputable def cbcOverStd : Realization (CBC F) (Std F) := (cbcOverHybrid F).comp (hybridOverStd F)
example : (cbcOverStd F).impl .ideal ⟨(), (k, iv, m₁, m₂, ())⟩ = cbc2Plain F k iv m₁ m₂ := rfl   -- literally the inlined program
```

So "the basic functionalities from which everything else is derived" is
literal: the trusted base is the set of `incl` realisations, which is the
MPC's price list, and every other functionality is a composite of
realisations down to that base. A change of MPC changes the base; a change
of implementation changes one morphism; neither touches a caller's proof.

### 2.11 What this buys: programs at the level of the functionality

A protocol is written against the functionalities it needs and proved
against their specifications. Every way of providing a functionality is
then a realisation that plugs in without touching the protocol or its
proof. For an AES-CBC protocol written in the AES-hybrid, the AES
functionality can be provided by:

| Realisation of `AES F aes`          | What it is here                                                        | Trusted base                           |
|-------------------------------------|------------------------------------------------------------------------|----------------------------------------|
| arithmetic program over the black box | `Realization (AES F aes) (Std F)`: S-boxes by inversion, linear layers free | the black box (the MPC's price list) |
| Boolean program (garbled-circuit style) | a realisation over a Boolean black box `[Lin GF2, Mult GF2, …]` with xor/and, plus a `Switch` at the boundary if the caller's shares are arithmetic | the Boolean black box, itself a primitive layer |
| hardware enclave                    | `Realization.incl`: AES is a *primitive* functionality, priced on the list, with the disclosure the enclave is trusted to have (nothing, or a declared side channel) | the enclave |

The protocol and its certificate are identical in all three cases,
because the interface, program and declared disclosure of `AES`, is the
contract. Two consequences deserve to be said out loud:

* **The framework proves the hybrid layer.** What is verified is that the
  protocol realises its specification given ideal functionalities, and
  that realisations compose. That the garbling protocol realises the
  Boolean black box, or that the enclave realises AES, is a statement
  about a protocol or a piece of hardware, outside this model and in its
  trusted base. The UC composition theorem is what joins the two. Which
  security notion the whole then inherits is *not* a consequence of
  `Realization.comp`: the simulators here are arbitrary `PMF` kernels
  with no efficiency certificate, and the realisation equation is about
  one request, not an interactive execution. Transferring the perfect
  hybrid step to a computationally secure base is a conditional, external
  application (it needs an efficient simulator and an interactive
  embedding, neither of which the framework provides); the framework
  supplies the hybrid step and nothing more (report, Scope decisions).
* **Representations meet at the interface.** A Boolean realisation works
  on bit shares and an arithmetic caller holds field shares, so the
  realisation includes the conversion (§2.9, §6.5) and its price includes
  the switch. Alternatively the AES functionality is stated generic in the
  field and each realisation fixes its own; either way the caller sees
  one `enc`.

The same holds one level up: the `CBC` functionality of
`Examples/AesHybrid.lean` is itself a specification, and a higher protocol
written against `CBC` never learns whether it is running on the hybrid
program, on a direct implementation, or on hardware.

**Terminology.** The latency notion is called *delay*: the length of the
critical path through a program's dependency graph under the per-operation
latencies of an MPC. Rounds are its unit. "Depth" is the special case where
every operation has latency one.

### 2.12 Interfaces and meaning: when a program has semantics

An interface is a *vocabulary*. `MulTriple.ops F` is one operation, `get`,
whose response has shape `share F × share F × share F`. Nothing else: no
distribution, no disclosure, no spec. A *functionality* is an interface
together with its meaning, and the library fixes **one ideal model per
functionality name**: `MulTriple F` says `get ↦ (a, b, a·b)` with `(a, b)`
uniform on `F²` and nothing declared, `Mult F` says `mult ↦ a·b`,
`Reveal F` says `reveal ↦ x`, public by shape. That binding is what the
name promises, and it is why a functionality is named after what it does:
`MulTriple`, not "triple", and `SquarePair` and `DoubleSharing` are
distinct functionalities although their responses have the same shape
(§6.1).

Since a hybrid is a list of functionalities and not of interfaces, the
type of a program,

```lean
def mulBeaver [Has (Lin F) fs] [Has (Reveal F) fs] [Has (MulTriple F) fs] (x y : D.sh F) : Prog fs.ops D (D.sh F)
```

reads "written using the linear, reveal and triple *functionalities*",
and its meaning is fixed the moment it typechecks: `fs.model` dispatches
to the components' ideal models and nothing else. (Decision 013 left a
functionality-indexed `Has` as the step still to take; the list hybrid
takes it, and it is now the only `Has`.) A `Prog fs.ops D α` is still a
syntax tree: which requests are made, in what order, and how each
continuation depends on the answers. Output, view, delay and cost are all
`run` under a model (§3).

"Instantiating" therefore means two different things, and only one of
them is needed for semantics:

* **Giving the interface its ideal model.** This happens when the
  functionality is defined, once, and is not a per-MPC choice. Every MPC
  that lists `MulTriple F` offers *that* functionality; the price list
  only says what it charges and cannot redefine what it means.
* **Realising the functionality** by a protocol, or by a program over
  other functionalities (`beaverMult`, `aesByProgram`). This never
  touches semantics. The program is a program in the hybrid where the
  functionality is ideal, its meaning is with respect to the ideal model,
  and a realisation carries the theorems across (§4.1,
  `handle_realizes`). That is the UC reading: a hybrid protocol is a
  program in the `F`-hybrid, and `F`'s ideal functionality is part of its
  definition.

This is the invariant stated in §7 from the other side: **a program has
semantics regardless of the MPC, but a cost only once an MPC is fixed.**
Semantics needs the functionality (fixed per name by its author); cost
needs the price list.

What the core keeps open, by leaving the model a parameter of `run`, is
the ability to interpret the same syntax in other ways: the
functionality's `eval` at `Id` for `rfl`, a cost model's timed model of
its interface for delay and communication, a hybrid model in which a
callee is abstract, or a deliberately wrong
functionality to state a counterexample (`BadMulTriple`,
`Examples/Beaver.lean`: same interface, `a = b`, still correct, provably
not a realisation). Those are other *interpretations* of one program, not
other meanings of "triple", and every theorem names the model it is about,
so nothing proved against `MulTriple F` can be mistaken for a statement
about `BadMulTriple F`.

## 3. Semantics

### 3.1 Models: one joint step, in a monad

```lean
structure Model (ι : Interface) (D : Domain) (m : Type → Type) where
  step : (r : Req ι D) → m (Resp ι D r.op × ι.leak r.op)     -- the response *and* the disclosure, jointly

def Model.det     (program : (r : Req ι D) → Resp ι D r.op) (leak : (r : Req ι D) → ι.leak r.op) : Model ι D m
def Model.silent  (program : (r : Req ι D) → Resp ι D r.op) : Model ι D m      -- every disclosure type `Unit`
def Model.lift    (m) (M : Model ι D Id) : Model ι D m                          -- an evaluation model, in any monad
def Model.program (M : Model ι D m) (r : Req ι D) : m (Resp ι D r.op)          -- the response marginal
```

A model says, for each request, what comes back and what is declared, as
one joint law. There is no separate `leak` accessor: the correlation
between response and disclosure is part of the specification (a public
coin whose value is disclosed but not returned, §6.3), and a
deterministic function of (request, response) could not express it. The
monad `m` is the one design decision of this section, and it is what
removed the coin tape:

* `m := PMF` (Mathlib's probability mass functions) is **the semantics**.
  `rand` is `uniform F` (`PMF.uniformOfFintype`); a Beaver triple is the
  image of a uniform draw from `Fin 2 → F`; a run is a distribution over
  (output, trace). Privacy is stated here and nowhere else.
* `m := Id` is **evaluation**. Deterministic functionalities (`Lin`,
  `Mult`, `Reveal`, `Cmp`, …) are modelled at `Id` once and lifted
  (`Functionality.ofEval`); randomised ones carry an `eval` model with
  the coins fixed to a dummy, so that costs and delays evaluate (values
  under it are meaningless by design). Coin-free programs compute output,
  view and cost by `rfl`/`decide`, and `dist_lift` says their `PMF`
  semantics is the point at that evaluation, so `rfl` proofs transfer to
  the semantics.
* `m := Sched := StateT Clock Id` is **scheduling**: the timed domain of
  §3.5, where a clock records what has been revealed.

The *ideal* domain identifies shares with values, `Domain.ideal := ⟨fun T
=> T⟩`; models are stated there. The models of `Std` are the obvious
ones: `mult ↦ a * b`, silent; `reveal ↦ x`, whose response is clear and
therefore in the trace by shape, nothing further declared. `Rand.model`
draws `uniform F`; `MulTriple.model` samples its correlation from a
*jointly* uniform `Fin 2 → F` (§6.1); `RandNZ.model` draws a uniform
nonzero element, for programs that mask by multiplication. There is no
tape and no coin index: each draw is a fresh `bind`, and `k` draws are one
draw from `F^k` (`seqUniform_eq_uniform`, §4.1). The model of a hybrid
dispatches by position to the model of the component, so the model of an
MPC is assembled functionality by functionality, like the list.

Functionalities carry no state of their own across requests. That is not
what makes `run_bind` hold: `run_bind` holds in every lawful monad, state
included, and is used at `Sched`. Statelessness is what makes the
per-request realisation equation compose: `handle_realizes` commutes the
simulator's coins for one request past the rest of the run
(`PMF.bind_comm`), which a hidden state shared between requests would
forbid. Stateful functionalities (persistent hidden state, interleaved
sessions, batched MAC checks, amortised preprocessing) are out of scope
for the foreseeable future; response-dependent callers are not what this
excludes, and are supported (report, Scope decisions).

### 3.2 Cost: paid by the instantiation, in the scheduling monad

```lean
structure Price where (delay : Nat) (comm : Nat)      -- what an MPC charges for an operation
structure Clock where (clock revealed comm : Nat := 0) -- control clock, reveal clock, communication so far
abbrev Sched := StateT Clock Id                        -- the cost monad

def delayOn (M : Model ι .timed Sched) (c : Prog ι .timed (Timed T)) : Nat := (Sched.output M c).time
def commOn  (M : Model ι .timed Sched) (c : Prog ι .timed α)         : Nat := (Sched.run M c).2.comm
```

A cost model instantiates each operation as a step in `Sched`: it
computes the response, stamps it with the round at which it is ready,
and adds the operation's communication to the counter. Delay is the
ready time of the output, computed from data dependencies (§3.5);
communication is the counter at the end. Both are read off one scheduled
run of the program in the timed domain, and neither is a property of a
functionality: the same program has another delay and another
communication under another MPC.

Two dependent multiplications (`mul3`) have delay 2 and communication 4
on `abb`; two independent ones feeding a third (`mul4seq`) still have
delay 2, for three multiplications' worth of communication. Delay does
not stack, and nothing has to say so per program: it falls out of the
dependency graph.

For a reactive program, whose shape depends on what it opens, cost is a
distribution; that is stated in the ideal domain with an additive cost
model (`CostModel ι C`, a price per operation in any Mathlib `AddMonoid`,
accumulated by the interpreter's trace; `costDist`, §3.4).

"Score different sub-functionalities differently" is a price list. Several
lists coexist for one hybrid, and for concatenated lists price lists
concatenate:

| Functionality | honest-majority rounds | preprocessing rounds | online triple generation | `total` (openings) |
|---------------|-----------------------:|---------------------:|-------------------------:|-------------------:|
| `Lin`         | 0                      | 0                    | 0                        | 0                  |
| `Mult`        | 1                      | (via `MulTriple`)    | (via `MulTriple`)        | 1                  |
| `Reveal`      | 1                      | 1                    | 1                        | 1                  |
| `Rand`        | 0 (PRSS)               | 0                    | 1                        | 0                  |
| `MulTriple`   | —                      | 0 (precomputed)      | 2                        | 0                  |
| `Cmp`         | e.g. 3                 | e.g. 2               | e.g. 4                   | e.g. 5             |

`Examples/Beaver.lean` has `preMPC` (triples precomputed, priced `⟨0, 0⟩`)
and `preOnline` (triples generated online, `⟨2, 3⟩`); the same Beaver
program has delay 1 and communication 2 under the first, 3 and 5 under
the second, all by evaluation.

### 3.3 The interpreter

```lean
def run (M : Model ι D m) (K : CostModel ι C) : Prog ι D α → m (α × Trace ι C)
  | .pure a   => pure (a, Trace.zero)
  | .call r k => do let p ← M.step r                                          -- (response, disclosure)
                    let res ← run M K (k p.1)
                    pure (res.1, Trace.seq ⟨K.op r.op, [⟨r.op, (ι.cod r.op).blank p.1, p.2⟩]⟩ res.2)

def output (M : Model ι D Id)  (c) : α                 := (Id.run (run M .unit c)).1
def view   (M : Model ι D Id)  (c) : List (Event ι)    := (Id.run (run M .unit c)).2.view
def cost   (M : Model ι D Id)  (K) (c) : C             := (Id.run (run M K c)).2.cost
def dist   (M : Model ι D PMF) (c) : PMF (α × List (Event ι)) := (fun p => (p.1, p.2.view)) <$> run M .unit c
```

One interpreter, written once for any monad, yields every observable, and
it records one event per request: the operation, the blanked response,
the sampled disclosure. The first two are not the model's to choose
(decision 014). Cost is orthogonal to semantics by construction: `output`
and `view` are computed under the unit cost model and provably do not
depend on the cost model (`run_fst`), and the cost model never sees
values. The only coupling is control flow: an `if` on an opened value
decides which branch's cost is paid, so cost depends on the *model*
exactly as far as the program's shape depends on opened data. For
straight-line programs it does not depend on it at all; in general it is
a distribution (`costDist`), as it should be.

The laws, proved once by induction on the free monad (`Model.lean`):

```lean
run_bind  : run M K (c.bind k) = do r ← run M K c; s ← run M K (k r.1); pure (s.1, r.2.seq s.2)  -- any lawful `m`
run_lift  : run (M.lift m) K c = pure (Id.run (run M K c))          -- a coin-free run is a point
dist_lift : dist (M.lift PMF) c = pure (output M c, view M c)       -- so `rfl` at `Id` is a theorem at `PMF`
dist_bind : dist M (c.bind k)  = do r ← dist M c; s ← dist M (k r.1); pure (s.1, r.2 ++ s.2)
dist_call : dist M (.call r k) = do p ← M.step r; res ← dist M (k p.1); pure (res.1, ⟨r.op, blank p.1, p.2⟩ :: res.2)
```

A concrete program that draws coins has its distribution *computed* by
`simp` with the `weft` simp set (the laws, the transports along `Has`, and
each standard functionality's model): `dist (Pre F).model (mulBeaver x y)`
unfolds to "draw `v` uniform on `Fin 2 → F`, output `x·y`, trace
`beaverView (x − v 0, y − v 1)`" in one call (`mulBeaver_dist`,
`Examples/Beaver.lean`), and the proof of privacy is then the mask lemma.
The tape semantics that used to be needed for evaluation is gone:
`Model.lift` and `dist_lift` give evaluation by `rfl` for exactly the
programs where evaluation makes sense, and `simp` does the rest. (Two
engineering notes from the sources: responses are taken apart by
projections, not patterns, and the scheduling state is threaded by
`StateT`'s own bind; either choice the other way makes evaluation by `rfl`
exponential in the number of requests.)

Structured share types (`Fin n → D.sh F`, records of shares such as
`Point D F` in the gallery) need nothing new on the program side: they are
Lean values holding handles. Responses of operations are described by a
`Shape` (`unit`, `clear T`, `share T`, products, vectors, lists), so that
their public part is structural; a Clean-style class mapping a Lean record
to a shape is worth adding for I/O ergonomics, but it is sugar.

### 3.4 Delay and communication compose exactly under the derived instantiation

A price carries both numbers per operation, but theorems mention one
resource at a time: `delayOn M.timed c` and `commOn M.timed c` read the
two off one scheduled run. `mul4seq` is 2 rounds and `chain3` is 3
rounds, both with three multiplications' worth of communication; each is
its own `rfl`.

**The exact instantiation of an abstract operation is to run its
implementation.** A caller written in a hybrid with an abstract operation
(`mulAdd`, `enc`) is costed by an MPC that instantiates that operation
somehow. If a realisation of the operation over the target hybrid is
known, the honest instantiation runs it:

```lean
/-- The timed model of `F` that runs `f`'s implementation in the target's cost model `T`. -/
def Realization.timed (f : Realization F fs) (T : Model fs.ops .timed Sched) : Model F.ops .timed Sched
abbrev MPC.derived (M : MPC) (f : Realization F M.hybrid) : MPC.Entry := ⟨F, f.timed M.timed⟩
def Realizations.timed (g : Realizations fs gs) (T : Model gs.ops .timed Sched) : Model fs.ops .timed Sched

/-- A scheduled run of the caller, every abstract operation instantiated that way, *is* the run of the
inlined program: same output, same clocks, same communication. -/
theorem Realizations.runOut_timed (g : Realizations fs gs) (T) (c : Prog fs.ops .timed α) :
    runOut (g.timed T) c = runOut T (Prog.handle (g.impl .timed) c)
theorem Realizations.delayOn_timed … : delayOn (g.timed T) c = delayOn T (Prog.handle (g.impl .timed) c)
theorem Realizations.commOn_timed  … : commOn  (g.timed T) c = commOn  T (Prog.handle (g.impl .timed) c)
```

This is exact by construction (`Cost.lean`, an induction on the caller
with `run_bind`), for every caller, reactive or not, and with the global
clocks included: the callee's reveals and barriers act on the caller's
clocks exactly as they would inlined. A hand-written model of the
abstract operation, one latency or a per-input profile, is an
*approximation* of this one; what it approximates is now a definition.
`Examples/Timing.lean` has one functionality `MulAdd` and three MPCs for
it (atomic, profiled, derived); `Examples/AesHybrid.lean` costs CBC in
the AES-hybrid with `enc` derived from the AES program and gets the
inlined numbers, 4 rounds and 8 units, by `rfl`.

**Composition for communication as a distribution** has the same shape
as composition for privacy. Call a handler *priced* under `K` if each
request's program has a cost independent of its operands and coins
(structurally scheduled):

```lean
def Priced (M : Model ι .ideal PMF) (impl : (r : Req κ .ideal) → Prog ι .ideal (Resp κ .ideal r.op))
    (K : CostModel ι C) (p : CostModel κ C) : Prop :=
  ∀ r, costDist M K (impl r) = pure (p.op r.op)

theorem cost_handle (g : Realizations fs gs) (hp : Priced gs.model (g.impl .ideal) K p)
    (c : Prog fs.ops .ideal α) (hc : Valid fs.model g.Pre c) :
    costDist gs.model K (Prog.handle (g.impl .ideal) c) = costDist fs.model p c
```

Inlining priced realisations into any valid caller costs what the caller
costs with each abstract operation priced at its implementation's cost
(proved, `Cost.lean`: by induction on the caller, `run_bind`, and the
fact that a realisation's result is distributed as the abstract
program's). So a protocol's communication complexity is stated once in
the hybrid with abstract prices, and instantiating AES by a program
substitutes that program's cost for the abstract price, with no new
analysis of the protocol (`Examples/AesHybrid.lean`: 20 units in the
hybrid with `enc` priced at 10, 8 once derived or inlined, by `rfl`).

**Hand-written models of an abstract operation are bounds at best.**
Under dependency tracking (§3.5) a single latency serialises the whole
implementation behind all of its inputs, and an implementation with a
"late" input (`mulAdd a b c = a·b + c` needs `c` only after the
multiplication) is over-counted; a **timing profile**, the longest path
from each input to the output inside the implementation,

    ready(out) = max (d₀, max_i (ready(in_i) + d_i))

is exact for a straight-line callee in isolation (`Examples/Timing.lean`:
atomic 2, profiled 1, derived 1, inlined 1). It is **not** exact in
general (report, Issue 10): the reveal and control clocks are global
state, so an inlined callee that reveals, computes in the clear and
inserts back waits on every earlier reveal of the *caller*, which no
per-input profile of the callee can know, and even `smul 1 x` after a
reveal at time `T` returns at `T` while its isolated profile is zero.
The clocks over-approximate dependency edges of weight zero whose source
the interpreter cannot see, because clear values carry no time. Whether a
hand-written model that *dominates* the derived one (later times, later
clocks, more communication, for every request and state) gives an upper
bound on every caller is a monotonicity statement about the interpreter
that needs the caller to be domain-generic, which Lean cannot know of a
program at the timed domain; it is not attempted (§8). What is kept:
`Barrier` and the control clock (the reveal-then-branch program
undercounts, 1 round instead of 3, without it). Known gap: a revealed
branch that selects an existing share with `pure` escapes the control
time.

So the round semantics is eager scheduling: no `∥` to write, delay and
communication computed by one run, and both composing exactly when an
abstract operation is instantiated by its realisation.

### 3.5 Delay is computed, not proved, and needs no `∥`

Round complexity is a pass over the program, and the user proves nothing
for a concrete program: the interpreter is the pass and `rfl` runs it.
There is no parallel node in the program language (decision 002):
parallelism is **computed from data dependencies**.

**Dependency tracking (`Timed.lean`).** Let every share carry the round
at which it is available. An operation's result is ready at
`max (operand times, clock) + latency`, and the round complexity of
a program is the ready time of its output: the critical path of the data
dependency graph. This is a *second domain*, because programs are
polymorphic in the domain, and a second monad, because the clock is state:

```lean
structure Timed (T : Type) where (val : T) (time : Nat)
abbrev Domain.timed : Domain := ⟨Timed⟩                       -- shares are timed, clear values plain
structure Clock where (clock revealed comm : Nat := 0)         -- control clock, reveal clock, communication
abbrev Sched := StateT Clock Id                               -- the scheduling monad

/-- One generic timed model for every interface, from the evaluation model and a price per operation:
ready at `max (operand times, clock) + delay`; an operation with a clear operand also waits for the reveal
clock; a clear response raises the reveal clock; `comm` is paid.  (`Barrier.timed` raises the control clock.)
Written without `let`, so that kernel evaluation is linear in the number of requests. -/
def Model.timed (E : Model ι .ideal Id) (p : ι.Op → Price) : Model ι .timed Sched
abbrev Functionality.priced (F : Functionality) (p : Price) : MPC.Entry := ⟨F, Model.timed F.eval fun _ => p⟩

def delayOn    (M : Model ι .timed Sched) (c : Prog ι .timed (Timed T)) : Nat := (Sched.output M c).time
def delayClear (M : Model ι .timed Sched) (c : Prog ι .timed α) : Nat := (Sched.run M c).2.revealed
def commOn     (M : Model ι .timed Sched) (c : Prog ι .timed α) : Nat := (Sched.run M c).2.comm
```

With this, sequential `do`-code gets the parallel count and no `∥` is
needed anywhere:

```lean
def mul4seq [Has (Mult F) fs] (a b c d : D.sh F) : Prog fs.ops D (D.sh F) := do
  let ab ← mul a b
  let cd ← mul c d          -- independent of ab: the pass sees it
  mul ab cd
-- delay 2 (rfl); the chain a·b·c·d is 3; the product tree with plain binds is its depth
```

Clear values stay plain, so generic programs branch on them as usual; what
the dependency graph cannot see about them, two clocks in the scheduling
state cover. The *reveal clock* is the latest time at which anything
became clear, and any operation with a clear operand (`const`, `smul`:
`Operands.hasClear (dom o)`) inherits it, since clear computation is opaque: a value
revealed at round 2, multiplied in the clear and inserted back with
`const`, carries round 2 into whatever uses it (`revealThenUse`, 3 rounds
by `rfl`). The *control clock* handles a branch on a revealed value whose
arms do not data-depend on it: the program says `barrier` (the `Barrier`
functionality, semantically a no-op, whose timed model is the one that is
not the generic one), which raises the
control clock to the reveal clock, so everything issued afterwards is
scheduled after the values it branched on (`binarySearch`: 3 levels × 4
rounds, 12 by kernel `decide`; 4 without the barrier). Reveal itself does
not raise the control clock, so independent reveals share a round
(Beaver's two openings). Semantics is untouched: the timed model computes
the same values, only tagged, and coins get a dummy value, which delay
never depends on.

For families ("`prodAll` on `n` elements is `⌈log₂ n⌉` rounds") the generic
technique is an induction using `run_bind` and `omega`, with the gallery
as templates. Proof-by-evaluation uses `rfl` and kernel `decide` only;
`native_decide` is never used.

## 4. Properties and the shape of proofs

All three are stated against a model, and for concrete programs all three
are proved by `rfl` / `decide`: the interpreter just runs.

```lean
-- correctness
example (a b c : F) : output (Std F).eval (mul3 (fs := Std F) (D := .ideal) a b c) = a * b * c := rfl
-- rounds (timed domain, inputs at round 0)
example (a b c : F) : delayOn (Std.timed F) (mul3 (fs := Std F) (D := .timed) ⟪a⟫ ⟪b⟫ ⟪c⟫) = 2 := rfl
example : delayOn (Std.timed F) (prodTree (fs := Std F) (D := .timed) depth2Tree) = 2 := rfl   -- 4 leaves, plain binds
-- the view is computed, not asserted
example (a b : F) : view (Std F).eval (openMul (fs := Std F) (D := .ideal) a b)
    = [⟨Std.mult F, (), ()⟩, ⟨Std.reveal F, a * b, ()⟩] := rfl
example (a b : F) : view (Std F).eval (leakyMul (fs := Std F) (D := .ideal) a b)
    = [⟨Std.reveal F, a, ()⟩, ⟨Std.reveal F, b, ()⟩] := rfl
```

### 4.1 Privacy: simulation at the level of the functionality

**Setting.** Every functionality is one joint step: what it returns and
what it declares. `rand` returns a share and declares nothing; `reveal`
returns a clear value, which is public by shape; `mult` returns a share
and declares nothing. A program is a program in the functionality-hybrid
model, and we prove it secure *there*. This is the arithmetic-black-box
methodology of Damgård–Nielsen and SPDZ: the UC composition theorem turns
"the program is secure given an ideal ABB" plus "the protocol realises
the ABB" into security of the whole, so the MPC protocol is never modelled
here. What remains to be simulated is exactly the trace of the program,
and the values inside shares (`⟦a⟧`, notation for a share of `a`) are
hidden by fiat.

**One shape of statement.** The semantics of a program is a distribution
over (output, trace), `dist M c : PMF (α × List (Event ι))`. Every privacy
statement is a realisation:

> *the program realises functionality `F`*

meaning: for every request, the joint distribution of (response, trace)
of the program equals `F`'s response paired with the output of a simulator
that is handed `F`'s event and nothing else, one equation between `PMF`s
(`Realization.lean`, §2.10, decision 015):

```lean
real : ∀ r, Pre r → dist fs.model (impl .ideal r) = do
  let (y, d) ← F.model.step r                                   -- the functionality's response and disclosure
  let s ← Sim ⟨r.op, (F.ops.cod r.op).blank y, d⟩               -- the simulator sees the event only
  pure (y, s)
```

Read it as: draw the response as the functionality draws it, let a
simulator that sees only the public record of that request (the
operation, the clear part of the response, the declared disclosure)
invent the trace, and the pair must be distributed as the real run. The
response stays in the joint: a hidden component may be opened later by
the caller, and the trace must be consistent with that opening. This is
why "`do reveal x; pure x` realises the identity" is false here
(`openKeep_not_realizes`, `Examples/Privacy.lean`), although a definition
that handed the simulator the output would have accepted it at the ideal
domain, where a share is its value (report, Issue 1). The usual
instances:

| The functionality realised                                   | reads as                                                    |
|--------------------------------------------------------------|-------------------------------------------------------------|
| returns `a·b` in the clear, declares nothing (`OpenMul`)     | `openMul` reveals nothing beyond its output (`openMulReal`) |
| returns `⟦a·b⟧`, declares nothing (`Mult F`)                  | Beaver's openings are pure noise (`beaverMult`)             |
| returns `⟦x⁻¹⟧`, declares nothing, for `x ≠ 0` (`Invert`, `Pre`) | inversion by masking, under a precondition (`invertReal`) |
| returns `⟦x₀ + r·x₁⟧`, discloses `r` (`RandComb`)             | a declared disclosure that is not a function of the output (`randComb2Real`) |
| every component of one hybrid over another (`Realizations (Std F) (Pre F)`) | the compositional notion (`stdOverPre`)     |
| contents of shares, given nothing                            | trivially, shares are hidden by fiat                        |

**Why the masks must be jointly uniform, and why that is a theorem
here.** A simulator has to produce the *whole trace* with the right joint
distribution, so every mask argument needs the whole vector of masks a
run draws to be uniform on `F^k`, not each coordinate uniform on `F`.
Coordinate-wise uniformity is not enough: Beaver with `a = b` (each
uniform) reveals `x − a` and `y − a`, whose difference is `x − y`.
Pairwise independence is not enough either: `r₁, r₂` independent uniform
and `r₃ := r₁ + r₂` are pairwise independent and each uniform, but
revealing `x − r₁`, `y − r₂`, `z − r₃` publishes `x + y − z`. Only joint
uniformity of the mask vector (equivalently, mutual independence of the
masks) makes the revealed vector the image of a uniform vector under a
bijection, which is the one fact every proof uses. In a tape semantics
this is an *assumption* about the measure on tapes, and the proof rule "a
bijection on tapes preserves it" is false for infinite tapes and a
counting argument for finite prefixes. In the `PMF` semantics it is a
*theorem*: each coin is a fresh `bind` of `uniform F`, and

```lean
theorem uniform_prod : (do a ← uniform α; b ← uniform β; pure (a, b)) = uniform (α × β)
theorem seqUniform_eq_uniform : seqUniform F n = uniform (Fin n → F)     -- n fresh draws = one draw from Fⁿ
```

(`PMF.lean`). Correlations draw their `k` coins as one uniform
`Fin k → F` outright (§6.1), so a triple's `(a, b)` is jointly uniform by
definition. `Examples/Beaver.lean` shows all of this on multiplication
from triples: one triple (`beaverMult`, a bijection of `F²`), two chained
multiplications (`mul3Beaver`: two calls are one draw from `F² × F²` by
`uniform_prod`, then a bijection of `F⁴`), and the counterexample
`BadMulTriple` whose `a` and `b` are each uniform but equal: the program
is still perfectly correct on it, and provably not a realisation of
`Mult F` (`mulBeaver_bad_not_realizes`, the opened pair publishes
`x − y`). This is the whole reason there is no tape and no bijection on
tapes anywhere: the only bijections in the development are on finite
types, in the one lemma that follows.

**The generic per-operation technique: the mask lemma.** Almost every
revealed vector in an MPC program is `v = f(secrets, masks)` with fresh
masks. If, for every value of the secrets, `masks ↦ v` is a bijection of
`F^k`, then `v` is uniform and independent of the secrets: the simulator
draws `v` fresh. Packaged once, as a fact about Mathlib's uniform
distribution:

```lean
theorem uniform_map_equiv (e : α ≃ β) : (uniform α).map e = uniform β
```

with the bijections coming from Mathlib's `Equiv` library: `Equiv.subLeft x`
for `a ↦ x − a`, `Equiv.mulLeft₀ x hx` for `s ↦ x·s` on the nonzero
elements, `Equiv.prodCongr` and `piFinTwoEquiv` to assemble vectors
(`maskEquiv`). The proof of `beaverMult` is: `simp only [weft]` with
`mulBeaver_dist` unfolds the run to "draw `v` uniform on `Fin 2 → F`,
output `x·y`, trace of `(x − v 0, y − v 1)`"; `ring` closes the output;
`uniform_map_equiv` with `(v 0, v 1) ↦ (x − v 0, y − v 1)` closes the
trace. Inversion by a nonzero mask (`invertReal`) is the same three steps
with `mulLeft₀`. This lemma is the one-time-pad lemma, the `rnd` rule of
EasyCrypt, the random-mask elimination step of maskVerif, and the affine
treatment of random values in λ_obliv, in one statement. It is also what a
tactic should automate: a trace entry of the form `x ± r` or `x · r` with
a fresh mask `r` is discharged by constructing the shift or scale
bijection.

**The adversary's view is the tagged trace, structurally.** The adversary
also sees *which* operations are invoked (the parties execute them, and
the program is public). So the trace of a run is one `Event` per request:
the operation; the clear part of the operands and of the response, by
shape (`Shape.blank`); and what the functionality declares. The first
three are recorded by `run` and no model can omit them: a model that
returned an opened value and declared nothing would still show it
(decision 014). The operation carries no share (operands are not part of
an `Event`), and it is what lets a simulator know that a `mult` happened
without seeing its inputs.

**Only realisations over structural events transport.** A privacy
statement that ignores the operation channel, "the list of opened values
is a function of the output", does not survive composition: a program
whose *shape* depends on a share's value at the ideal domain has
different traces for different inputs with the same opened values (the
report's `shapeLeak`). So every leaf proof is stated as a realisation, and
the old "over `add` and `mul` alone everything is hiding" becomes
`arith_private` (`Examples/Silent.lean`): over a hybrid whose
functionalities declare nothing and return only shares, a program
realises its own output distribution *if its trace is the same list for
every input*, a public-trace hypothesis that a straight-line program
satisfies and a share-dependent one does not.

**Composition: a verified program is a functionality.** A primitive
operation has a joint step. A verified program gets the same thing: its
functionality is its spec, and its declared disclosure is what its
simulator is given. Callers treat the program as one more functionality of
the hybrid, prove their own certificate against that abstract model, and
never look inside. The definitions and the theorem that make this sound
(`Realization.lean`), all proved:

```lean
/-- Realisations of every component of `fs` over `gs`; `g.impl`, `g.Pre`, `g.Sim` dispatch by position. -/
inductive Realizations : Hybrid → Hybrid → Type 1
  | nil : Realizations [] gs
  | cons : Realization F gs → Realizations fs gs → Realizations (F :: fs) gs

/-- Every request `c` issues, on the support of its run under `M`, satisfies `P`. -/
inductive Valid (M : Model ι .ideal PMF) (P : Req ι .ideal → Prop) : Prog ι .ideal α → Prop
  | pure a : Valid M P (.pure a)
  | call r k (hr : P r) (hk : ∀ z ∈ (M.step r).support, Valid M P (k z.1)) : Valid M P (.call r k)

/-- Inlining realised operations into any valid caller: the concrete run is the abstract run with each
event replaced by its simulation. -/
theorem handle_realizes (g : Realizations fs gs) (c : Prog fs.ops .ideal α) (hc : Valid fs.model g.Pre c) :
    dist gs.model (Prog.handle (g.impl .ideal) c) = do let r ← dist fs.model c; let s ← simList g.Sim r.2; pure (r.1, s)

theorem output_transport : … → Prod.fst <$> dist gs.model (Prog.handle (g.impl .ideal) c) = Prod.fst <$> dist fs.model c
def Realization.comp (f : Realization F fs) (g : Realizations fs gs) : Realization F gs
  -- impl := inline;  Sim := f.Sim then simList g.Sim;  Pre r := f.Pre r ∧ Valid fs.model g.Pre (f.impl .ideal r)
def Realization.incl (F) (gs) [Has F gs] : Realization F gs        -- Sim replays the event at F's position
```

Read `Realization` as: the simulator is given only the event (operation,
clear outputs, declared disclosure), never a hidden component of the
response and never an operand, and must reproduce the concrete trace
jointly with the response. `handle_realizes` is the UC composition
theorem at the level of this semantics: induction on the caller's
free-monad trace, `dist_bind` at each `call`, the realisation equation
for that call, and one commutation of independent draws
(`PMF.bind_comm`: the simulator's coins for this call do not interact with
the rest of the run). `Realization.comp` is why functionalities and
realisations form a category (§2.10); `output_transport` is the payoff
for a caller's correctness, and `comp` itself for its privacy: a caller
certified in the hybrid is a certificate over the target by one
application.

Preconditions ride along. A realisation's guarantee holds for requests
satisfying `Pre`; a caller discharges it by `Valid`, every request it
issues, on the support of its ideal run, satisfying the precondition
(`Valid.of_forall` when there is none to discharge, `Valid.bind` for
sequential composition, `invertFresh_valid` for a real one, §7), and the
composite's `Pre` records what is still owed.

Worked instance: Beaver realises `Mult F` over `Pre F`, and with the two
trivial realisations this is `stdOverPre : Realizations (Std F) (Pre F)`
(`Examples/Privacy.lean`). Hence *every* program over the arithmetic
black box transports to the preprocessing functionality with Beaver
inlined, with no new proof (`transport_std_pre`, `output_std_pre`);
`openMulOverPre := (openMulReal F).comp (stdOverPre F)` is a certificate
over `Pre F` obtained the same way; `b2aReal` realises a `B2A`
functionality with nothing declared over a daBit hybrid; and an entire AES
functionality realised by a program gives `cbcOverStd`
(`Examples/AesHybrid.lean`).

So privacy proofs compose exactly as programs do: prove each program once
as a realisation of its functionality, and prove callers in the hybrid
where that functionality is primitive. Nothing is redone when a callee's
implementation changes, as long as the new one still realises the same
functionality. This is what Clean's local subcircuit proofs become in MPC:
the local proof is a realisation, and the functionality is the interface.
Sequential composition of two certified programs needs no primitive of
its own: it is a two-call caller in the hybrid.

**A subtlety about transitivity.** "X given Y" is *not* transitive in
general: from "X simulatable given Y" and "Y simulatable given Z" one
cannot conclude "X given Z". Take a secret `i : ZMod 2`, a fresh uniform
`Z`, `Y := ()` and `X := i + Z`. "X given Y" holds (`X` is uniform
whatever `i`) and "Y given Z" holds trivially, but "X given Z" needs a
simulator `Sim z = pure z` when `i = 0` and `pure (z + 1)` when `i = 1`,
which depends on the secret. The compositional statements are therefore
always about the *joint* view: a realisation reproduces (response, trace)
jointly, and `comp` composes two joint statements rather than chaining
two conditionals. This is the same reason UC keeps the environment in the
definition: what is simulated is the whole view, not one projection at a
time. It is also why the compositional notion conditions on the callee's
*event* and not on its output: a callee's share output is a hidden handle
nobody sees, and a simulator that needed it could not be run by the
caller's simulator.

**Statistical privacy** is the same statement with the output marginal
exact and the joint within `ε` in total variation, per operation
(`RealizationStat`, `Statistical.lean`); a perfect realisation is one with
`ε = 0` (`Realization.toStat`), and zero distance is equality
(`PMF.eq_of_statDist_eq_zero`). The bound is on the joint, not the view
alone: over `𝔽₂`, `b ← rand; reveal (x + b); pure b` has a uniform view
for every `x` while a later opening of `b` reveals `x`. The kernel lemma
that makes errors add is proved, `PMF.statDist_bind_le`: the distance of
two binds is at most the distance of the first draws plus the expected
distance of the continuations. The caller's `budget` (the sum, over its
ideal execution, of the per-request errors) is defined; the theorem that
`handle_realizes` holds up to `min 1 (budget …)` is described in §8 and
not yet stated in Lean.

**What is proved, and what is not.** The compositional theorems exist and
none is `sorry`: `handle_realizes`, `output_transport`,
`Realization.comp`, `cost_handle`, `Realizations.runOut_timed`,
`PMF.statDist_bind_le`. Described here but not yet stated in Lean, let
alone proved: the statistical budget theorem just mentioned, and the
bound that a dominating hand-written cost model gives (§3.4), which
needs a parametricity hypothesis on the caller.

**Related work that shaped this.**

* Damgård & Nielsen 2003, and SPDZ (Damgård, Pastro, Smart, Zakarias
  2012): the arithmetic black box and programs as programs over it.
  Damgård, Fitzi, Kiltz, Nielsen, Toft 2006 and Catrina & de Hoogh 2010:
  the standard "the opened value is uniform because the mask is fresh"
  privacy arguments for ABB sub-protocols, which the mask lemma packages.
* Canetti 2001 (UC), Lindell "How to simulate it": the real/ideal
  definition `Realization` specialises, and the composition theorem that
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
  random-mask elimination; the closest formal ancestor of `Realization`.
* Darais, Sweet, Liu, Hicks 2020 (λ_obliv): uniform random values as
  affine resources in a type system, giving probabilistic obliviousness
  by typing; the discipline a `masked` tactic would check.
* Barthe, Grégoire, Zanella-Béguelin (EasyCrypt) and Barthe et al. 2017
  on couplings: bijection-based equidistribution as the proof rule.
  Brzuska et al. 2018 (state-separating proofs) and SSProve 2021:
  modular packages with local simulators composed by a hybrid argument,
  which is the shape of `Realization` plus `handle_realizes`. IPDL
  (Gancher et al. 2023): equational simulation proofs for protocols,
  including MPC.
* Wysteria / Wys★ (Rastogi, Hammer, Hicks 2014; Rastogi, Swamy, Hicks
  2019) and Viaduct (Acay et al. 2021): mixed-mode MPC languages whose
  security is stated over an ideal functionality, with information-flow
  labels doing the bookkeeping our `Has`/domain typing does.

### 4.2 Generic programs, generic theorems

Programs are polymorphic in `fs` and `D`; theorems can be too. Cost
bounds are best stated for *any* price list that prices the
functionalities a certain way. The shape (schematic; the examples state
these for concrete sizes):

```lean
theorem inner_comm (pMult pReveal : Price) (xs ys : List (Timed F)) :
    commOn (Std.timed F pMult pReveal) (inner (fs := Std F) (D := .timed) xs ys) = pMult.comm * (xs.zip ys).length
```

This reads "on the black box at any prices, inner product costs one
multiplication per pair", and it holds for every price. Delay bounds have the same shape against
`M.timed`, with the caveat of §3.4 once a bound is composed through a
realisation.

## 5. Composition

Proofs about `bind` reduce to proofs about the pieces, in any lawful monad:

```lean
run_bind  : run M K (c.bind k) = do r ← run M K c; s ← run M K (k r.1); pure (s.1, r.2.seq s.2)
dist_bind : dist M (c.bind k)  = do r ← dist M c; s ← dist M (k r.1); pure (s.1, r.2 ++ s.2)
dist_call : dist M (.call r k) = do p ← M.step r; res ← dist M (k p.1); pure (res.1, ⟨r.op, blank p.1, p.2⟩ :: res.2)
dist_lift : dist (M.lift PMF) c = pure (output M c, view M c)
```

(all by induction on `c`; `run_bind` needs only that costs form a
monoid). With these in the `weft` simp set, the distribution of a
concrete program normalises to closed form (a uniform draw, then a
point), and privacy proofs reduce to the mask lemma.

**Handlers.** `Prog.handle : ((r : Req ι D) → Prog κ D (Resp ι D r.op)) →
Prog ι D α → Prog κ D α` implements every request of `ι` by a program
over `κ`. The library does this for multiplication
(`Examples/Beaver.lean`, `Examples/Privacy.lean`):

```lean
def mulBeaverFrom [Has (Lin F) fs] [Has (Reveal F) fs] (triple : Prog fs.ops D (D.sh F × D.sh F × D.sh F))
    (x y : D.sh F) : Prog fs.ops D (D.sh F) := do
  let (a, b, c) ← triple
  let u ← sub x a
  let e ← reveal u              -- e = x − a
  let v ← sub y b
  let d ← reveal v              -- d = y − b: independent of the first reveal, same round (§3.5)
  … -- x·y = c + e·b + d·a + e·d, linear from here

program beaverMult : Realization (Mult F) (Pre F) where            -- the certificate
  impl D r := match r with | ⟨.mult, (x, y, ())⟩ => mulBeaver x y
  Sim _ := (uniform (F × F)).map (beaverView F)
  real r _ := by …                                                  -- unfold the run, then the mask lemma

/-- Every component of `Std F` over `Pre F`: linear operations and reveal by themselves, `Mult` by Beaver. -/
noncomputable def stdOverPre : Realizations (Std F) (Pre F) :=
  .cons (Realization.incl (Lin F) (Pre F)) (.cons (beaverMult F) (.cons (Realization.incl (Reveal F) (Pre F)) .nil))
-- Prog.handle ((stdOverPre F).impl D) : Prog (Std F).ops D α → Prog (Pre F).ops D α      -- Std programs run on Pre
```

This is the mechanism for

* realising a functionality on top of others (`Mult` as above; `Cmp` via
  bit decomposition; `Rand` via `MulTriple`), and
* deriving cost, output and view of the composite from those of the
  realisations: cost of `handle h c` under `K` equals cost of `c` under
  the model that prices each operation at the cost of its implementation
  (`cost_handle`); the output distribution is unchanged
  (`output_transport`); the view of `handle h c` is the view of `c` with
  each event simulated (`handle_realizes`), so realisations composed with
  a certified caller give a certificate over the target
  (`Realization.comp`). These are the theorems that make the library
  modular, and they are proved (`Realization.lean`, `Cost.lean`).

`Prog.weaken` (a program over a smaller hybrid runs on a larger one,
`Incl`) is the degenerate handler, and `Realizations.incl` is its
certificate.

## 6. Correlated randomness

Everything an MPC hands out at random is one of three things, and each has
one place in the design.

### 6.1 Primitive correlations: a function of fresh coins

A correlation is a deterministic function of `k` uniform coins. That is the
whole definition. Each correlation is its own functionality, named after
what it promises (decision 013), and `Correlation` is the generic way to
give it a model (`Std/Random.lean`):

```lean
structure Correlation (R T : Type) where
  k     : Nat
  build : (Fin k → R) → T

noncomputable def Correlation.sample (c : Correlation R T) : PMF T :=
  (uniform (Fin c.k → R)).map c.build            -- the k coins are drawn *jointly* uniform on Rᵏ

namespace MulTriple
inductive Op where | get
abbrev ops (F : Type) : Interface where            -- the interface
  Op := Op
  dom _ := []
  cod _ := .prod (.share F) (.prod (.share F) (.share F))
def corr (F : Type) [Mul F] : Correlation F (F × F × F) := ⟨2, fun x => (x 0, x 1, x 0 * x 1)⟩
noncomputable def model (F : Type) : Model (ops F) .ideal PMF :=            -- sample the correlation, declare nothing
  ⟨fun _ => (corr F).sample.map fun t => (t, ())⟩
end MulTriple
abbrev MulTriple (F) : Functionality := ⟨MulTriple.ops F, MulTriple.eval F, (· = MulTriple.model F), …, MulTriple.timed F⟩
```

The response shape describes a sample in terms of the domain, so the same
functionality works for every representation of shares; `build` is
written once, at the ideal domain, where a share is its value.
`SquarePair` and `DoubleSharing` have the same response shape and are
different functionalities: a program asking for one cannot be handed the
other.

| Correlation        | response shape                        | coins | `build`                                  |
|--------------------|---------------------------------------|------:|------------------------------------------|
| random share       | `share F`                             | 1     | `x 0`                                    |
| square pair        | `share F × share F`                   | 1     | `(x 0, x 0 * x 0)`                       |
| Beaver triple      | `share F × share F × share F`         | 2     | `(x 0, x 1, x 0 * x 1)`                  |
| double sharing     | `share F × share F`                   | 1     | `(x 0, x 0)`                             |
| matrix triple      | `vec n (vec m (share F)) × …`         | nm + mk | `(A, B, A·B)`                          |
| random bit         | `share F`                             | 1 bit | needs the bit alphabet, §6.4             |
| daBit              | `share F × share GF2`                 | 1 bit | `(embed b, b)`, cross-field, §6.5        |
| random permutation | `vec n (share F)`                     | Fisher–Yates | needs a `Fin`-valued alphabet, §6.4 |

The double sharing row makes a general point: in the black box, `[r]_t` and
`[r]_2t` are the same value seen twice, because sharing degree is not
observable there. If a program must respect degrees (it may only add
same-degree shares, it needs a `reduce` operation to go from `2t` to `t`),
index the share type by the degree (a phantom parameter on the clear type,
so that `D.sh` tells them apart) and type the operations accordingly. The
ideal model still identifies the values; the types stop the program from
misusing them. The same move handles authenticated versus unauthenticated
shares, or shares over different rings.

### 6.2 Assembling correlations: the offline phase is a program

A correlation that the MPC does not hand out natively is *assembled* from
ones it does, and the assembly is a program, certified as a realisation
in the sense of §5:

```lean
/-- Triples from random shares and one secure multiplication. -/
def tripleFromRand [Has (Rand F) fs] [Has (Mult F) fs] : Prog fs.ops D (D.sh F × D.sh F × D.sh F) := do
  let a ← rand F
  let b ← rand F                  -- independent: one round
  let c ← mul a b
  pure (a, b, c)
```

Under the offline list `[Lin F, Mult F, Rand F]` with `rand` free and
`mult` one round, `Examples/Basic.lean` checks by `rfl` that assembling a
triple costs one round and two units; its
output distribution is that of `MulTriple.corr`, two fresh draws being one
draw from `F²` (`uniform_prod`). The last point is the one that matters:
packaged as a `Realization (MulTriple F) [Lin F, Mult F, Rand F]` with a
simulator that replays the three silent records, it replaces the
preprocessing box under any caller and preserves that caller's certificate
(the composition theorem of §5).

Two assemblies that *do* open something, and are still private because
what they open is independent of everything (both need `Field F`; they
are described here and not in the examples):

```lean
/-- Random bit (odd characteristic): open r², take a square root. -/
def bitFromRand (sqrt : F → F) : Prog fs.ops D (D.sh F) := do
  let r ← rand F
  let s ← mul r r
  let v ← reveal s                       -- opens r², uniform on squares, independent of r's sign
  let t ← smul (1 / sqrt v) r           -- ±1
  let one ← const 1
  let u ← add t one
  smul (1/2) u                          -- (±1 + 1)/2 ∈ {0, 1}

/-- Random share with its inverse (Bar-Ilan–Beaver): open r·s for fresh r, s. -/
def randInv : Prog fs.ops D (D.sh F × D.sh F) := do
  let r ← randNZ F
  let s ← randNZ F
  let p ← mul r s
  let v ← reveal p                       -- opens r·s, uniform on the nonzero elements, independent of r
  let sInv ← smul (1 / v) s             -- s / (r s) = 1/r
  pure (r, sInv)
```

Their certificates are the Beaver pattern: the simulator draws a fresh
coin and reports it, and the mask lemma says the opened value is that
coin. For `randInv` the map is `s ↦ r·s`, a bijection of the nonzero
elements when `r ≠ 0`: with `randNZ` for both masks the proof is perfect,
with plain `rand` it holds only off `r = 0`, which is exactly the
statistical slack the real protocol has (§8).

**Offline versus online is a cost split, not a semantic one.** Price the
same functionality differently on two lists: `MulTriple F` costs
`⟨0, 0⟩` on `preMPC` (precomputed) and `⟨2, 3⟩` on `preOnline`
(generated online), and the single interpreter reports the difference
(`Examples/Beaver.lean`: 2 versus 5 units, 1 versus 3 rounds). "This
program needs `n` triples" is a cost model charging one unit per `get`.

### 6.3 Public coins

A public coin is a correlation whose sample everybody sees. Its response
is *clear*, so it is in the trace by shape; nothing further needs to be
declared:

```lean
namespace PubCoin
abbrev ops (F : Type) : Interface where
  Op := Op                                  -- coin
  dom _ := []
  cod _ := .clear F                         -- public by shape
noncomputable def model (F : Type) : Model (ops F) .ideal PMF := ⟨fun _ => (uniform F).map fun x => (x, ())⟩
end PubCoin

/-- A random linear combination of shares, challenge chosen after the shares exist. -/
def randomCombination [Has (Lin F) fs] [Has (PubCoin F) fs] (xs : List (D.sh F)) : Prog fs.ops D (D.sh F) := do
  let r ← coin F
  …                                         -- Σ rⁱ · xᵢ, all linear
```

The distribution of `randomCombination [a, b]` is "draw `r`, trace
`[coin ↦ r, smul r, add, …]`, return `⟦a + r·b⟧`". It is *not* hiding in
the old sense, and the old claim that it was is false (report, Issue 5):
the response and the coin are correlated, and a caller that later opens
the result learns both. Its honest specification is a functionality
`RandComb` whose joint step draws `r`, returns `⟦x₀ + r·x₁⟧` and
*discloses* `r`, a disclosure that is not a function of the response (on
all-zero inputs the response is `0` for every `r`), which is exactly what
a joint `step` can say and a deterministic `leak (request, response)`
could not. `randComb2Real` (`Examples/RandomCombination.lean`) realises
it: the simulator reads `r` off the event and replays the three records.
This is the pattern for MAC checks, batched openings and any "challenge"
step.

### 6.4 Several coin alphabets

Bits, `Fin n` values (for permutations) and elements of a second ring are
not functions of a uniform field element in odd characteristic, so a
single alphabet of coins would not do. With coins as distributions there
is nothing to do: each functionality's ideal model draws from the uniform
distribution on whatever finite type it needs (`uniform F`,
`uniform (Fin (2 ^ m))`, `uniform {x // x ≠ 0}`, `uniform (Fin k → F)`),
and independence across functionalities is `bind`. The trace needs no
shared alphabet either: each event carries its clear outputs and its
disclosure at the type the operation declares (§2.9).

### 6.5 Cross-field correlations: edaBits

An edaBit is a random `r < 2^m` shared over the arithmetic field together
with its `m` bits shared over `𝔽₂`. In the field-generic design of §2.9 it
is a functionality whose sample spans two fields, and `𝔽₂` (`GF2 :=
ZMod 2`) is just another field (`+` is xor, `*` is and), so Boolean
programs are ordinary `Lin`/`Mult` programs over `GF2`
(`Examples/MultiField.lean`):

```lean
namespace EdaBitF
abbrev ops (F : Type) (m : Nat) : Interface where
  Op := Op                                                 -- get
  dom _ := []
  cod _ := .prod (.share F) (.vec m (.share GF2))          -- r, and its m bits (LSB first)
noncomputable def model (F : Type) [NatCast F] (m : Nat) : Model (ops F m) .ideal PMF :=   -- a uniform r < 2^m, its bits
  ⟨fun _ => (uniform (Fin (2 ^ m))).map fun r => ((((r.val : ℕ) : F), bitsOf m r.val), ())⟩
end EdaBitF
abbrev EdaBit (F : Type) [NatCast F] (m : Nat) (coin : Nat := 0) : Functionality   -- `coin` fixes the mask under `eval`
```

The canonical use is arithmetic-to-binary conversion: reveal `x - r`, then
add the public value back onto the shared bits with a binary adder. The
adder is branch-free (a public bit multiplies, it never `if`s), which is
both the right program and what lets evaluation run on symbolic inputs:

```lean
/-- Ripple-carry addition of a public `c` to shared bits: xor free, and one round; `m` rounds. -/
def addPublic [Has (Lin GF2) fs] [Has (Mult GF2) fs] :
    (m : Nat) → (Fin m → GF2) → (Fin m → D.sh GF2) → D.sh GF2 → Prog fs.ops D (Fin m → D.sh GF2)
  | 0, _, _, _ => pure fun i => i.elim0
  | m + 1, c, r, carry => do
    let t ← add (r 0) carry                   -- r₀ ⊕ carry
    let cb ← const (c 0)
    let s ← add t cb                          -- s₀ = c₀ ⊕ r₀ ⊕ carry
    let rc ← mul (r 0) carry                  -- r₀ ∧ carry          (the one round)
    let ct ← smul (c 0) t                     -- c₀ ∧ (r₀ ⊕ carry)   (public bit: free)
    let carry' ← add rc ct                    -- maj(c₀, r₀, carry)
    let rest ← addPublic m (Fin.tail c) (Fin.tail r) carry'
    pure (Fin.cons s rest)

/-- A2B: reveal `x - r`, then `x = (x - r) + r` bit by bit. -/
def a2b (F : Type) [CommRing F] [Encodable F] (m : Nat) (coin : Nat := 0)
    [Has (EdaBit F m coin) fs] [Has (Lin F) fs] [Has (Reveal F) fs] [Has (Lin GF2) fs] [Has (Mult GF2) fs]
    (x : D.sh F) : Prog fs.ops D (Fin m → D.sh GF2) := do
  let (r, rbits) ← edabit F m coin
  let d ← sub x r
  let c ← reveal d                            -- the only revealed value
  let zero ← const (0 : GF2)
  addPublic m (bitsOf m (Encodable.encode c)) rbits zero

abbrev mixed : MPC := [(Lin (ZMod 17)).priced ⟨0, 0⟩, (Mult (ZMod 17)).priced ⟨1, 2⟩, (Reveal (ZMod 17)).priced ⟨1, 1⟩,
                       (Lin GF2).priced ⟨0, 0⟩, (Mult GF2).priced ⟨1, 1⟩, (EdaBit (ZMod 17) 4 3).priced ⟨0, 0⟩]
```

Checked by evaluation (the evaluation model with the mask fixed to `3`):
the opened values are `[x - 3]` and nothing else (`rfl`), the
communication is 5 and the last bit is ready at round 4, one reveal round
plus three carries (kernel `decide`), and `a2b 5` yields the bits of `5`. Privacy is the
Beaver pattern with one coin, perfect when `r` is uniform in the field
(`ℤ/2^k` with `m = k`) and statistical when `r < 2^m` masks a value in a
larger field, which is what a statistical realisation's `ε` (§4.1, §8) is
for. B2A, truncation and comparison via edaBits are the same ingredients
in a different order.

**daBits** (Rotaru–Wood 2019) are the simplest cross-field correlation:
one uniform bit `b`, shared over `F` and over `𝔽₂` (`DaBit F`, ideal
model `(uniform GF2).map fun b => ((b, b), ())`). Boolean → arithmetic
conversion is one reveal: open `c = x ⊕ b` in `𝔽₂`, then
`x = c + b − 2·c·b` in `F`, linear in `⟦b⟧_F` since `c` is public
(`b2a`). A program spanning both worlds, `hammingWeight`, converts each
bit and sums in `F`: all conversions are independent, so one round for
any number of bits (`decide` on the timed model), one revealed bit per
input, and the count comes out as an arithmetic share. Its privacy is
the mask lemma over `𝔽₂`: the revealed `x ⊕ b` is uniform for either
`x`, by the bijection `b ↦ x + b` (`b2a_dist`, `b2aReal` realising the
`B2A` functionality), and the output is `x` in `F` with certainty
(`fin_cases` on the two bits).

Switching itself is not special: `Switch F G` is one more functionality
with an ideal model, exactly like `Mult F`, and a switch implemented via
edaBits is a realisation of it.

## 7. Specifications are functionalities; certificates are realisations

Clean's `FormalCircuit` bundles a circuit with `Assumptions`, a `Spec` and
the proofs, so that a caller uses the spec and discharges the assumptions
without unfolding the callee. Here there is no separate bundle (decisions
006, 015; report, Issue 4): the specification *is* a functionality,
written by its author as a total joint step, and the certificate is a
`Realization` of it, whose `Pre` is the assumption and whose `real` is
correctness and privacy in one equation, the output marginal being part
of the joint. The old `Gadget`, which certified a program against its own
output distribution and blocked composition on its assumptions, is gone;
so is `Hiding`, which handed the simulator the output.

```lean
/-- Inversion, silent: returns `⟦x⁻¹⟧`, declares nothing. -/
abbrev Invert : Functionality :=
  .ofEval ⟨Unit, fun _ => [F], fun _ => .share F, fun _ => Unit, fun _ => false, fun _ => false⟩
    ⟨fun r => pure (r.args.1⁻¹, ())⟩

/-- Inversion by masking realises silent inversion for `x ≠ 0`: the simulator draws a fresh uniform
nonzero element and presents it as the opened value (`s ↦ x·s` is a bijection of the nonzero elements). -/
program invertReal : Realization (Invert F) (InvHyb F) where
  impl D r := invert r.args.1
  Pre r := r.args.1 ≠ 0
  Sim _ := (uniform {t : F // t ≠ 0}).map fun t => invView F t.1
  real r hx := by …                     -- `invert_dist`, field algebra on the support, `Equiv.mulLeft₀`

/-- A caller discharges the precondition on the support of its own ideal run. -/
theorem invertFresh_valid : Valid (CallerHyb F).model (fun r => … a.1 ≠ 0 …) (invertFresh F) := …
```

Three choices are visible here (decisions 005, 009, 011):

* **Correctness is perfect, and it is in the joint.** The output marginal
  of the equation is the functionality's response; for a coin-free
  program that is `rfl`. There is no set of "good coins": a program that
  needs an invertible mask asks the functionality for one (`RandNZ`, a
  uniformly random nonzero share, a priced functionality like any other)
  rather than gambling on the coins.
* **Assumptions are preconditions on requests, discharged by `Valid`.** A
  polymorphic caller cannot state `x ≠ 0` about a share, and UC
  functionalities are total; so the precondition lives on the
  realisation, at the ideal domain, and a caller discharges it by
  `Valid`: every request it issues, on the support of its ideal run,
  satisfies it (`invertFresh_valid`: the support of `RandNZ` is the
  nonzero elements). `Realization.comp` accumulates it: the composite's
  `Pre` is the outer one together with validity of the outer program for
  the inner preconditions. The total alternative, a functionality that
  returns `⟦x⁻¹⟧` with `0⁻¹ = 0` and discloses whether `x = 0`, is
  realised by the same program with no precondition; the caller pays the
  disclosure instead (`InvertTotal`, `invertTotalReal` in
  `Examples/Inversion.lean`: the simulator reads the zero test off the
  event).
* **No price.** A program has semantics regardless of the MPC, but a
  cost only once an MPC is fixed: its `output` and `view` are determined
  by the functionalities it calls, the same everywhere; its delay and
  communication need that MPC's latencies and bandwidths. So a bound is a
  separate theorem about the pair: the same `invert` has delay 2 or 3
  depending on the MPC (`invMPC`, `invMPC'`; decision 005).

**The `program` command** (`Program.lean`, `Examples/Checked.lean`) is how
certificates are built. It declares the `Realization` and then checks the
fully applied `impl` as it sits in it: every constant it uses,
transitively through the package's definitions, is computable, not
`unsafe`, `partial` or `implemented_by`; no parameter of the certificate
mentions a domain. Simulators and proofs are unconstrained (the simulator
is a `PMF`, so the certificate is `noncomputable`). This is what makes
"the simulator sees only the event" mean what it says: an implementation
that could inspect a share (`peekIdeal`, fixed at the ideal domain;
`peek`, with classical decidable equality; a `peekAt` callback passed as
a parameter) is rejected, and the honest `keepReal` passes. How the check
binds to a certificate obtained through `comp` is recorded as open in the
report.

**Composition** is by specification. Callers are written in the hybrid
where the functionality is primitive, and `handle_realizes` (§4.1)
transports their proofs; sequential composition of two certified programs
is the two-call caller `do o ← op g₁ i; op g₂ o`, whose trace is the two
events, which is the only thing a composite could honestly declare (the
intermediate output is a hidden, possibly random handle, so a composite's
trace cannot be a function of its own input and output alone). A
capability class (§2.5) whose instances all realise one functionality
gives the "same interface, several implementations, prices differ"
pattern for free.

## 8. Extensions, in the order they will be needed

1. **Statistical composition.** `RealizationStat` exists,
   `PMF.statDist_bind_le` (`bind` is a contraction in total variation,
   data-processing) is proved, and `budget` is defined; what is missing
   is the theorem that `handle_realizes` holds up to
   `min 1 (budget fs.model ε c)` for a valid caller. Needed for edaBit
   masking of a bounded value by a longer one (§6.5).
2. **Bounds from hand-written cost models** (§3.4): that an abstract
   operation's atomic or profiled model, when it dominates the derived
   one, bounds every caller's delay and communication from above. Exact
   composition is done (`Realizations.runOut_timed`); the bound needs
   monotonicity of the interpreter in the scheduling state, which holds
   only for domain-generic callers, a hypothesis Lean cannot state about
   a program at the timed domain.
3. **Adaptive environment.** Party inputs that depend on earlier
   openings: make the model's step a function of the trace so far.
4. **Corruption.** Tag disclosures with recipients (`revealto p`), the
   trace includes corrupt parties' inputs; both are instances of `disc`.
5. **Abort / malicious.** An abort response in the shape language
   (`Option` and sums are still to be added to `Shape`); privacy then also
   quantifies over adversarial abort choices.
6. **Static round bounds.** A syntactic over-approximation of delay that
   does not run the program, for programs with data-dependent control
   flow.

Not planned: stateful functionalities (hidden state across requests,
sessions, batching); the `PMF` realisation layer models fresh per-request
calls, and those need a different layer (report, Scope decisions).

## 9. Proof methodology, summarised

| Property           | Concrete program                      | Generic program                         |
|--------------------|---------------------------------------|-----------------------------------------|
| correctness        | `rfl` / `decide +kernel` / `ring`; on the support for coins | `simp [weft]` + algebra; `output_transport` |
| delay / cost       | `rfl`                                 | `simp [run_bind]` + `omega`; `cost_handle` |
| privacy (coin-free) | `dist_lift`, `rfl`: the simulator replays the trace | `arith_private`, under a public-trace hypothesis |
| privacy (coins)    | `simp [weft]` unfolds the run; `uniform_map_equiv` with an `Equiv` | `handle_realizes`, `Realization.comp` |
| not private        | two inputs, evaluate (`leakyMul_not_realizes`, `openKeep_not_realizes`) | —                        |

Evaluation means `rfl` or kernel `decide`; `native_decide` is not used.

## 10. Names

The name is **Weft** (chosen 2026-09-05): the threads a protocol weaves
across the parties; short, an English word, and free of collisions. The
working name had been *Glean* ("to glean": gather scraps of information;
the adversary gleans only what the program opens), which had the same
shape as Clean, the sibling ZK framework. It was dropped because it
collides with Meta's code-index tool and Mozilla's telemetry SDK, and the
repository was already `weft`. The Lean namespace is `Weft`.

The alternatives that were considered, kept for the record: a one-word
English word that puns on Lean, or rhymes with it, or says what MPC does.

* **Convene** — parties convene to compute; rhymes with Clean.
* **Unseen** — hiding; rhymes with Clean.
* **Screen** — screens values from view; also a stage on which things run.
* **Oblean** — oblivious + Lean.
* **Veil** — hiding, short, not a Lean pun.
* **Between** — a secret is split between parties.
* **Seal**, **Shroud**, **Curtain** — hiding metaphors, no Lean pun.

Avoid *Shamir*, *Beaver*, *SPDZ*-derived names: the framework is
explicitly protocol-agnostic.

## 11. Open questions

* **Universes.** `Shape`, `Interface` and `Functionality` are in `Type 1`
  because they quantify over response types; programs and models are in
  `Type → Type`. Harmless so far; if it bites (universe issues in Mathlib
  interop), index shapes by a code for the response type instead.
* **Parallelism is computed.** `bind` never parallelises, and there is no
  parallel node; the timed domain reads the dependency graph (decision
  002). A program whose branch on a revealed value is not a data
  dependency must say `barrier`; forgetting it under-counts, which a
  syntactic check ("every `if` on a revealed value is preceded by a
  barrier") could enforce.
* **Mathlib is the base.** The library depends on Mathlib and uses its
  definitions wherever one exists: `Field`, `CommRing`, `Inv` and `ZMod`
  for fields (`ring`/`field_simp` close the algebra), `Equiv` for the mask
  lemma, `PMF` and `uniformOfFintype` for the semantics, `AddMonoid` for
  costs, `Fin m →` vectors, `Encodable` where a conversion needs a
  canonical representative. See `decisions/010-mathlib.md`.
* **Coin alphabet.** None to choose: each functionality draws from the
  uniform distribution on the finite type it needs, and independence
  across draws is `bind` (§6.4).
* **Evaluation scales like evaluation.** Closing theorems by `rfl` runs
  the interpreter inside `whnf`; closed instances over `Fin 7` use
  `decide +kernel`, an order of magnitude faster at that size. Both are
  fine for examples and for concrete small programs. Real proofs go
  through the compositional lemmas (§5), which never evaluate the
  program, and through specifications (§7), which never unfold callees.
* **Equality of programs.** Do we want an equational theory (independent
  calls commute up to cost/trace-equivalence) or only observational
  equivalence via `run`? Observational is enough for everything above.
* **Recorded as open in the report.** The duplicate-entry and reindexing
  policy for list hybrids and price lists; the response shapes still to
  be added (`Option`, sums, clear-indexed dependent pairs); how the
  `program` check binds to a certificate obtained through `comp`; the
  timing contract (the `barrier` discipline, random public control flow,
  the `pure`-selection gap).
