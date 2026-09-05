# Review of the Glean privacy definitions

Date: 2026-09-05. Scope: the privacy definitions (`Hiding`, `Realizes`,
`Gadget`, `Functionality`/`Realization`, the tagged view), how they compose,
whether they mean what DESIGN.md says, and whether they can be satisfied
vacuously. Two independent passes (Claude, Codex) followed by a
cross-examination round; disagreements and their resolution are in
Appendix B.

What was not done: the old repository and the redesigned `PMF` layer were
not compiled. The checkout has no `.lake` directory and Mathlib was not
fetched. Every counterexample below is by unfolding the definitions as
written; the `randomCombination` one was also checked by exact arithmetic.
The core-only sketches of the new design listed in Appendix C were
typechecked separately in core Lean 4.29. Lean snippets marked "sketch"
are proposed shapes, not compiled code.

Ground rule agreed with the author: a functionality may declare any
`program` and any `leak`. That is the specification and it is trusted.
"You can write a leaky spec" is therefore not a finding. What counts is:
given the honest primitive models as written (`Std.ideal`, `Pre.ideal`,
`Rand.ideal`, `MulTriple.ideal`), can a statement be proved about a circuit
or implementation that is obviously not private, or can a claim in the
prose be shown false.

---

## 1. Summary

**Status (2026-09-05).** All ten issues discussed with the author and
decided; the decision is recorded under each issue, the resulting design is
stated once in "Final design" (authoritative), and Section 5 lists every
change as old → new → why. Five Codex/GPT review rounds; the last one
checked this record for consistency and its edits are applied. Two decisions were revised during the
discussion and both revisions are recorded in place (Issue 1 item 3; Issue
4 item 6). Nothing in the repository has been changed except this file.

| # | Issue | Severity | Decision |
|---|-------|----------|----------|
| 1 | `Hiding` hands the simulator the whole output, including secret shares | high | simulator sees the declared disclosure only; result stays in the joint; `Hiding` folds into `Realizes` |
| 2 | The `kind` function may carry the request payload, trivialising `Realizes` | high | request = operation + share operands; header is the operation, structural; three-channel event |
| 3 | Untagged models never see circuit shape; "no peeking" is not enforced | high | structural events; domain-generic statements; computable `program` command on the fully applied term; Lean DSL kept; programs, not circuits |
| 4 | `Gadget` certifies against its own output; assumptions block composition | medium | functionalities all the way; `Gadget` removed; `Pre` on realisations with `Valid`; hybrid = list, `Has` = one equality |
| 5 | Deterministic `leak` cannot express a random public disclosure; `randomCombination` claim is false | medium | joint `step` (5A) |
| 6 | `RealizesStat` permits output error; no composition lemma | medium | exact output marginal + TV on the joint (6A) |
| 7 | Leaf proofs are untagged; the composition theorem needs tagged | medium | restated as realisations (consequence) |
| 8 | Public inputs have no slot; clear request payloads are invisible | medium | public inputs are operation payload (consequence) |
| 9 | Prose contradicts code in several places | low | list of edits, applied with the definitions |
| 10 | Delay "composes exactly with profiles" is unproved and false as stated | medium, outside privacy focus | downgrade to upper bound (10A) |

What is right and should stay: the `PMF` semantics; joint uniformity as a
theorem (`seqUniform_eq_uniform`) with the `BadMulTriple` counterexample;
composition resting on the interpreter laws plus independence of fresh
per-call simulation in the stateless `PMF` model (`run_bind` and
`PMF.bind_comm`, Compose.lean:57); `Realizes` conditioning on the declared
leak and pairing with the response (the correct UC shape, strictly stronger
than `Hiding`); the tagged trace as an idea (it becomes the structural
event); the proved theorems `handle_realizes`, `Realizes.comp`,
`output_transport` (`Hiding.transport` goes with `Hiding`); `PMF.statDist`
(it is total variation).

---

## 2. Issues, with options

Each issue: where it is, what the definition says in plain terms, why that
is wrong, a concrete counterexample, the options, and a recommendation.

### Issue 1. `Hiding` declassifies the whole output

**Where.** `Glean.lean:482`.

```lean
def Hiding (M : Model σ L PMF) (c : I → Circ σ α) : Prop :=
  ∃ Sim : α → PMF (List L), ∀ i,
    dist M (c i) = do
      let y ← Prod.fst <$> dist M (c i)
      let s ← Sim y
      pure (y, s)
```

**What it says.** There is one simulator, working for every input `i`,
that is given the output `y` and must reproduce the revealed values so
that (output, reveals) has the right joint distribution.

**Why that is wrong.** The simulator sees `y` in full. When `α` is a clear
type that is the intended reading ("reveals nothing beyond the output").
When `α` is a share type, the ideal domain `Domain.ideal F := ⟨F, F⟩`
(`Glean.lean:90`) makes the share equal to its value, so the simulator is
handed the secret inside a handle nobody in the real protocol can see.

**Counterexample** (honest `Std.ideal`, no new models):

```lean
/-- Open the secret, then return the same share. -/
def openKeep {D : Domain} {σ : Sig} [Has (Reveal D) σ] (x : D.S) : Circ σ D.S := do
  let _ ← reveal x
  pure x

-- dist = pure (x, [x]).  Simulator: Sim y := pure [y].
theorem openKeep_hiding (F : Type) [Add F] [Mul F] [Sub F] :
    Hiding ((Std.ideal F).lift PMF) (fun x : F => openKeep (D := .ideal F) (σ := Std _) x) :=
  Hiding.of_lift _ _ (fun y => [y]) fun _ => rfl
```

The circuit broadcasts its input and is "hiding". It also holds on the
tagged model with `Sim y := pure [(2, [y])]`. Every headline proof in the
repo (`beaver_hiding`, `mulBeaver_hiding`, `b2a_hiding`, `cbc2Plain_hiding`)
is in fact strong, because each simulator ignores `y`; but the theorem
statements do not record that, and a reader cannot tell a strong proof from
a weak one. Codex notes `b2a_hiding` is the weakest: its output
`(x.val : ZMod 17)` identifies the input bit, so a conversion that opened
the bit would satisfy the same statement.

Note that this is not "every share-returning circuit is hiding". Returning
fresh randomness while revealing an independent input still fails. The
defect is automatic declassification of the entire result.

**Why pairing with `y` must stay.** The environment in UC sees honest
outputs, and a hidden share may be opened later by a caller. The joint
distribution with the hidden value is what a later opening observes, so it
must be preserved. Only what the *simulator receives* is wrong.

**Options.**

*Option 1A. Explicit public projections.* Give the simulator only what is
declared public, on both sides.

```lean
-- sketch
def Hiding (M : Model σ L PMF) (c : I → Circ σ α)
    (pubIn : I → P) (pubOut : α → Q) : Prop :=
  ∃ Sim : P → Q → PMF (List L), ∀ i,
    dist M (c i) = do
      let y ← Prod.fst <$> dist M (c i)
      let s ← Sim (pubIn i) (pubOut y)
      pure (y, s)

-- "reveals nothing at all": Beaver, inversion, a2b
example : Hiding (Pre.ideal F) (fun p : F × F => mulBeaver p.1 p.2) (fun _ => ()) (fun _ => ())
-- old definition, only for a clear output
abbrev Hiding.public (M) (c : I → Circ σ α) := Hiding M c (fun _ => ()) id
```

Cheap, mechanical, and it also gives the "given corrupt inputs" row of the
DESIGN §4.1 table (`pubIn` = the corrupt party's inputs). Two readings must
not be confused: `pubOut := fun _ => ()` demands a trace independent of the
result (Beaver satisfies this); `pubOut := id` allows the trace to depend on
the result once public. The first is stronger than "nothing beyond the
output".

*Option 1B. One notion: `Hiding` as a one-operation `Realizes`.* A circuit
with a declared disclosure is a one-op functionality; privacy is that its
circuit realises it. This removes the duplicate definition and makes the
declared disclosure explicit and reviewable.

```lean
-- sketch
def Hiding (M : Model σ L PMF) (kσ) (c : I → Circ σ α) (declared : I → α → List L) : Prop :=
  Realizes kσ (fun _ => ()) (circHandler c) M
    (Functionality.ofCircuit (fun i => Prod.fst <$> dist M (c i)) declared).model
```

*Option 1C. Distinct share type at the ideal domain.* `Domain.ideal F :=
⟨F, Share F⟩` with `structure Share (F) where val : F`. Misuse becomes
visible (`Sim` would have to call `.val`) but not impossible. Weak on its
own; useful alongside 1A.

**Recommendation.** 1A now (every existing proof adapts by supplying `()`
projections); 1B as the long-term single notion.

**Decision (2026-09-05).**

1. `Sim` receives exactly the **event** of the abstract operation
   (operation, clear outputs, declared disclosure; Issues 2 and 5) and
   nothing else: never a hidden response component, never an operand. The
   full return value stays in the joint `(y, s)`: hidden components are not
   leaked by the program, they are leaked when a later `reveal` opens them,
   and the joint is what makes the earlier trace consistent with that
   opening; clear components are public immediately, by shape.
2. **There is no separate `Hiding` API** (superseded by Issue 4: top-level
   privacy is a `Realization` of an independently specified one-operation
   functionality). The first recording here, "`Hiding M c declared` with an
   equivalence theorem", is history: Issue 4 wins.
3. `declared` (a gadget's) and `leak` (a functionality's) are the
   **specification of what the adversary learns**. They may be any function
   of the request, operands included, and the response: "returns `[a·b]`
   and leaks `a − b`", "leaks the high bit", "leaks whether `x = 0`" are
   ordinary functionalities. They are trusted like `program`. (First
   recorded as "clear data only"; corrected 2026-09-05 after the author's
   example. Codex's position in Appendix B stands.) What is constrained is
   only the automatic part: the simulator never receives the response, and
   the request header is structural (Issue 2).
4. Notation, as transparent `abbrev`s, no wrappers:
   `Leak L := List L` (one request's disclosure, also `declared`),
   `View L := List L` (a run's trace); when tagged, `Record K L := K × Leak L`,
   `TView K L := List (Record K L)`. `Sim : Leak L → PMF (View L)`.

What changes (recorded, not applied):

- `Hiding`, `HidingStat` (Glean.lean:482-493), `hiding_of_pure`,
  `Hiding.of_lift` (Glean.lean:496, 518), `Hiding.transport`
  (Compose.lean:83), `hiding_of_silent` (Silent.lean:65) are removed
  (Issue 4); `Gadget.simulatable` (Gadget.lean:45) with `Gadget`.
- Every existing theorem restated as a realisation of a one-operation
  functionality, no harder proof: `openMul_hiding` and
  `leakyMul_not_hiding` against a spec with clear output; `beaver_hiding`,
  `mulBeaver_hiding`, `mul3Beaver_hiding`, `mulBeaver_bad_not_hiding`,
  `b2a_hiding`, `Arith.hiding` (with a public-trace hypothesis),
  `cbc2Hybrid_hiding`, `cbc2Plain_hiding` against specs with `leak := []`.
- New regression example: `openKeep` is not `Hiding … (fun _ _ => [])`.
  `randomCombination` cannot be stated with a share result; it returns
  `(r, ⟦Σ rⁱxᵢ⟧)` with `declared _ p := [p.1]`, or waits for Issue 5.
- Prose: DESIGN §1:45-52, §4.1:893-925 (definition and the "X given Y"
  table), §9 table, decision 008 "Revisited" on `Hiding'`.

### Issue 2. The `kind` function may carry the payload

**Where.** `Realizes`, `Privacy.lean:113`; `Functionality.kind`,
`Functionality.lean:30`; decision 012.

```lean
def Realizes (kσ : {β : Type} → σ β → Kσ) (kτ : {β : Type} → τ β → Kτ)
    (impl : {β : Type} → τ β → Circ σ β) (Mσ : Model σ L PMF) (Mτ : Model τ L PMF) : Prop :=
  ∃ Sim : Kτ → List L → PMF (List (Kσ × List L)), ∀ {β : Type} (o : τ β),
    dist (Mσ.tagged kσ) (impl o) = do
      let y ← Mτ.program o
      let s ← Sim (kτ o) (Mτ.leak o y)
      pure (y, s)
```

**What it says.** The simulator sees the request's "kind" and the declared
leak, and must reproduce the concrete view. Decision 012 says the kind
"carries no payload" and the simulator "never sees the request's payload".

**Why that is wrong.** `kτ` is any function into any `Type`. Nothing stops
it from returning the secret arguments.

**Counterexample.**

```lean
def payloadKind (F : Type) : {β : Type} → Mult (.ideal F) β → F
  | _, .mult x _ => x

/-- Reveal x, then multiply. -/
def exposeMul (F : Type) [Add F] [Mul F] [Sub F] :
    {β : Type} → Mult (.ideal F) β → Circ (Std (.ideal F)) β
  | _, .mult x y => do
    let _ ← reveal (D := .ideal F) x
    mul (D := .ideal F) x y

-- Realizes Std.kind (payloadKind F) (exposeMul F) ((Std.ideal F).lift PMF) ((Mult.ideal F).lift PMF)
-- with Sim x _ := pure [(2, [x]), (1, [])].  Both sides: pure (x * y, [(2, [x]), (1, [])]).
```

An implementation that opens one input realises honest multiplication,
whose declared leak is empty. `Realization AES ABB` with
`AES.kind (enc k m) := (k, m)` would be a meaningless certificate, and
`Realization` is presented as a standalone artefact (`aesCircuit`, `sqRev`,
`cbcOverABB`). This does not extend to randomised functionalities (the
payload does not give the hidden random response), but every deterministic
one is affected.

A second problem is the opposite coarsening: `Std.kind` (`Privacy.lean:166`)
maps `const`, `add`, `sub`, `smul` all to `0`, so the adversary is modelled
as unable to tell which linear operation ran, or with which public
constant. In a real ABB all of that is public.

**Options.**

*Option 2A. Canonical kinds in the library, one per constructor, indexed by
the clear field, never containing shares.*

```lean
-- sketch
inductive StdPublic (F : Type) where
  | const (c : F) | add | sub | smul (c : F) | mult | reveal

def Std.public {D : Domain} : {β : Type} → Std D β → StdPublic D.F
  | _, .inl (.const c)          => .const c
  | _, .inl (.add _ _)          => .add
  | _, .inl (.sub _ _)          => .sub
  | _, .inl (.smul c _)         => .smul c
  | _, .inr (.inl (.mult _ _))  => .mult
  | _, .inr (.inr (.reveal _))  => .reveal
```

`Std.public` is polymorphic in `D` and its result type mentions only
`D.F`, so it cannot carry a share. `Functionality` then needs
`ops : Domain → Sig` (every signature already is), `K : Type → Type`, and
`kind : ∀ D {β}, ops D β → K D.F`. A fixed `K : Type` cannot work because
`D.F` varies with the domain.

*Option 2B. Derive kinds from a signature schema.* Describe each signature
first-order (constructor name, public arguments, share arguments, response
shape); interpret the schema at `D` for requests and at the erased domain
`⟨D.F, Unit⟩` for observations; prove the erasure laws once. Removes the
hand-written functions, but needs the schema infrastructure and a universe
adjustment (a `Σ β, τ ⟨F, Unit⟩ β` lives in `Type 1`).

*Option 2C. Keep user kinds but require a "no share dependence" proof.*
Cannot be stated without 2B's schema, so it collapses into 2B.

**Recommendation.** 2A now, one `Public` type per library signature; 2B if
the library grows past a handful of signatures.

**Decision (2026-09-05).** The cleanest form, not the easiest (Codex round
3 concurred, "adopt with changes"; its notes are folded in):

1. **A request is an operation applied to share operands.** The operation
   is everything public about the request (which primitive, its clear
   arguments): `const 7` and `const 3` are two operations, `add` is one
   operation with two operands. Operands are shares, typed by the clear
   type they share (`D.S : Type → Type`, as `MultiField.Domain`); a share is
   a share, there are no sharing-discipline sorts in the black box.
   Response shapes are a small closed language over types
   (`clear T | share T | unit | prod | vec`), so the public part of a
   response is structural (`blank`).
2. **The header is the operation.** There is no `kind` parameter anywhere:
   not in `Realizes`, not in `Functionality`, not in `Model.tagged`, which
   is deleted. Nothing user-written decides what the adversary sees of a
   request; the four `Lin` operations are distinct and `const c` shows `c`.
3. **The event recorded by the interpreter has three channels**:
   `(operation, clear outputs, declared leakage)`. Operation and clear
   outputs are structural; leakage is the disclosure component of the
   functionality's joint `step` (Issue 5), trusted (item 3 of Issue 1). The
   interpreter samples `step` once and uses both components of that sample.
   `Reveal`'s disclosure is empty, since its output is already public by
   shape. A model cannot omit a public output or invent a header.
   `Sim : Event τ → PMF (List (Event σ))`.
4. **Interfaces belong to functionalities, never to bundles.** A hybrid's
   interface is derived by indexing its list of functionalities (Issue 4
   item 6; the sum machinery of `Design.lean` is an obsolete
   demonstration); `Std`/`Pre` abbreviate lists. A new functionality is a
   signature (`Op`, `dom`, `cod`) and a model (one joint `step`, Issue 5).
5. **Consequences kept from Codex round 3:** named constructors stay the
   surface language (smart constructors over the structural core); prices
   are per operation and cannot see an operand; "offers this operation
   family" stays separate from per-operation pricing; operational models
   stay parameterised by the domain, and one generic timed model serves
   every interface; operand *identity* (wiring) is not in the view and is
   recorded as an explicit assumption under Issue 3 (circuits are
   parametric); `Silent.Arith.hiding` needs a public-trace hypothesis;
   universes stay small because interfaces are instantiated at concrete
   fields.
6. **Evidence.** The core (sorts, shapes, interfaces, requests, circuits,
   `Has`, `run` with structural events, Beaver over the preprocessing
   interface, a two-field circuit, the generic timed model) typechecks in
   core Lean 4.29 (`Design.lean` in the session scratchpad); the `PMF`
   layer is stated with the same shapes as today (revision 2 of the sketch
   has no sorts and restores `Barrier`). Migration is the whole sketch (all
   14 modules); prototype on one multiplication realisation and one
   mixed-field example first.

### Issue 3. Untagged models never see circuit shape, and "no peeking" is not enforced

**Where.** `Model.tagged`, `Privacy.lean:88`; the claim at DESIGN §2.3
lines 153-161; `Hiding`, `Gadget.circ` (`Gadget.lean:32`),
`Realization.impl` (`Functionality.lean:37`).

**What the prose says.** "Since `D.S` is an abstract type, the only
functions from `D.S` to anything are the ones the signature offers. A
circuit cannot look at a share." And: the adversary's view is the tagged
trace.

**Why that is wrong, part one (untagged view).** The untagged model records
only leaked values. Which operations ran, and how many, is not in the view,
so a circuit whose shape depends on a secret is "hiding".

```lean
def shapeLeak (F : Type) [Add F] [Mul F] [Sub F] [DecidableEq F] (x : F) : Circ (Std (.ideal F)) Unit :=
  if x = 0 then do let _ ← mul (D := .ideal F) x x; pure () else pure ()

-- untagged: dist = pure ((), []) for every x, so Hiding with Sim _ := pure []
-- tagged:   x = 0 gives [(1, [])], x ≠ 0 gives [];  same output, so not Hiding
```

`hiding_of_silent` (`Silent.lean:65`) proves empty declared leakage, not
absence of observable operation structure.

**Why that is wrong, part two (enforcement).** `shapeLeak` is written at the
ideal domain and branches on a share's value. `Hiding`, `Gadget.circ` and
`Realization.impl` accept such programs directly. Even a `D`-polymorphic
circuit can branch on shares:

```lean
open Classical in
def peek {D : Domain} {σ : Sig} [Has (Mult D) σ] (a b : D.S) : Circ σ D.S :=
  if a = b then mul a a else mul a b        -- noncomputable, typechecks
```

Lean has no parametricity theorem; "enforced by typing" is a convention.

**Options.**

*Option 3A. Mandate tagged models in every privacy statement, with complete
kinds (Issue 2).* Secret-dependent shape is then *detected* (the proof
fails honestly), not prevented. Delete the untagged `Hiding`.

*Option 3B. State privacy about polymorphic families and adopt a
computability convention.* Make the statement quantify over the domain, so
ideal-domain programs like `shapeLeak` cannot even be passed:

```lean
-- sketch: I, O : Domain → Type; c must be given for every domain
def Hiding (M : Model (σ (.ideal F)) L PMF) (c : ∀ D, I D → Circ (σ D) (O D))
    (pubIn : I (.ideal F) → P) (pubOut : O (.ideal F) → Q) : Prop := …  -- as in 1A, applied at c (.ideal F)
```

And require, by convention, that `c` is a computable definition (Lean's
`noncomputable` checker rejects `peek`). Residual trust: instance arguments
such as `[DecidableEq D.S]`, `[BEq D.S]` or a `measure : D.S → Nat` reopen
the hole, as do secrets captured outside the quantified family;
`implemented_by`/`extern` separate the executable from the kernel term.
This is a review checklist, not enforcement.

*Option 3C. A checked first-order front-end.* A small syntax `Src` with
share wires, public expressions and public control flow, an elaboration
`elab : Src → ∀ D, Circ (σ D) …`, and privacy theorems about `elab s`.
This is decision 001's rejected alternative revived as a *front-end* only:
`Circ` stays the semantic core, `do`-notation is lost at the surface. Heavy;
it is the only real enforcement.

**Recommendation.** 3A and 3B now; document the residual trust in a
decision record; 3C when the library is large enough that review does not
scale.

**Decision (2026-09-05).**

1. Views are structural events (Issue 2), so there is no untagged model;
   secret-dependent operation sequences are detected, not prevented.
2. Privacy statements take the domain-generic circuit (`c : ∀ D, …`) and
   instantiate the ideal domain themselves; an ideal-domain-only program
   cannot be stated (see the recorded example below).
3. Computability is enforced by `def`; a `program` command closes the
   remaining gaps. Amended after GPT round 4: the check runs on the
   **fully applied** implementation term as it sits in the certificate
   (every constant computable, no free hypotheses over `D.S`, closed apart
   from public parameters), not on a constant's name, because a computable
   domain-generic constant applied to a classical callback or a
   `[DecidableEq (D.S T)]` dictionary reintroduces share inspection at the
   use site. `Realization.impl` is quantified over the domain,
   `impl : (D : Domain) → (r : Req F.ops D) → Prog G.ops D …`, and the
   equation instantiates it at the ideal domain; `Realization` values are
   built only through the command. `Sim` and proofs may be classical.
4. Operand identity is not part of the view, and need not be. The Lean
   program *is* the circuit; it does not emit one. Which shares an
   operation is applied to is part of the program, and the program is
   public, so the simulator has it (together with the public inputs and
   revealed values that select the branch). `if s = 0 then mul x x else
   mul x y` is not detected, but is not a `program` (it branches on a
   share). This is why the discipline of items 2-3 is required. A
   handle-tagged domain (Codex round 3, Q4) is not needed.
5. The Lean DSL (free monad, `do`-notation, Lean continuations) stays;
   no first-order circuit syntax, not even as a deferred option (author's
   call, consistent with decision 001). Enforcement is items 2-3.
6. `Silent.Arith.hiding` is restated with a public-trace hypothesis.
7. Naming: the objects are programs in a hybrid; they open values, compute
   in the clear and branch on public values, so "circuit" (straight-line)
   is misleading as the general name. `Circ` becomes `Prog`, "circuit"
   becomes "program" throughout DESIGN.md; the checked declaration command
   is `program`; "circuit" is kept for the straight-line special case where
   a theorem needs it (the `barrier` discipline, a public-trace
   hypothesis). "Protocol" stays for the realisation of a functionality.

**Recorded example (2026-09-05): how a user states "communication Y, delay X,
in the `[Has mul] [Has lin]` hybrid, with empty leakage", and why the
statement must take the domain-generic circuit.**

The circuit is written once, with the domain `D` a parameter; each theorem
instantiates `D` and a model. "In the hybrid" is the circuit's type.

```lean
-- in the Lin/Mult hybrid, for every domain D and every MPC κ offering those two
def dotPlus {D : Domain} {κ : Interface} [Has (Lin F) κ] [Has (Mult F) κ]
    (xs ys : List (D.S F)) (c : F) : Circ κ D (D.S F) := do
  let ps ← (xs.zip ys).mapM fun p => mul p.1 p.2
  let s ← sumAll ps
  let k ← const c
  add s k

-- communication Y: ideal domain, the MPC's prices (prices see operations only)
theorem dotPlus_comm (xs ys : List F) (c : F) :
    cost hm.eval hm.comm (dotPlus (D := ideal) xs ys c) = 2 * xs.length := …
-- delay X: the same definition at the timed domain
theorem dotPlus_delay (xs ys : List (Timed F)) (c : F) :
    delayOn hm.timed (dotPlus (D := timed) xs ys c) = 1 := …
-- empty leakage: the domain-generic definition realises the one-operation functionality
-- "⟨xs, ys⟩ + c, leak []" over the hybrid.  The simulator gets the event (dotPlus n c, (), [])
-- and emits the n multiplication events and the linear events (`const c` shows c), which
-- depend only on the public n and c.
def dotPlus_private : Realization (DotPlus n c) hm :=
  ⟨fun D r => dotPlus (D := D) …, Sim, proof⟩          -- impl for every D; checked by `program`
-- Assumptions made explicit: xs and ys of equal length n (zip), n ≥ 1 for the delay of 1,
-- inputs available at round 0, mult latency 1, linear operations latency 0.
```

By contrast, a definition whose type fixes the domain before the body is
written is not a program in any hybrid:

```lean
def shapeLeak (x : F) : Circ (Std (.ideal F)) Unit :=      -- x is a share AND a field element
  if x = 0 then do let _ ← mul x x; pure () else pure ()
```

The body can branch on `x` because its type gave it `F`, not `D.S F`. The
current `Hiding`, `Gadget.circ`, `Realization.impl` accept it because their
argument type is `Circ σ α` with `σ` already at the ideal domain. The change
is only to the statement's argument type: it takes the family (`dotPlus`,
not `dotPlus (D := ideal)`) and instantiates it itself, so `shapeLeak`
cannot be passed. The three theorems above keep their meaning.

**Computability is enforced by Lean for a `def`.** Checked on Lean 4.29:

```lean
def peek {D : Domain} {T : Type} (a b : D.S T) : Bool := by
  classical
  exact if a = b then true else false
-- error: failed to compile definition, consider marking it as 'noncomputable'
--        because it depends on 'Classical.propDecidable'
```

So a computable, domain-generic body can do nothing with an `x : D.S T`
except pass it to an operation. Not enforced by Lean: `noncomputable def`,
and lambdas written inline in a theorem statement. Closing that is a small
metaprogram, a `circuit` command or `@[circuit]` attribute that checks at
declaration time: not `noncomputable`/`partial`/`unsafe`/`implemented_by`;
type quantifies over the domain; no hypothesis mentions `D.S` other than
the operands (no `[DecidableEq (D.S T)]`, no `measure : D.S T → Nat`).
Privacy certificates are produced by the `program` command, which checks
the **fully applied** implementation term at certificate construction
(Issue 3 item 3, as amended), not a declaration's name. A first-order
program syntax would be stronger; rejected, the Lean DSL stays.

### Issue 4. `Gadget` certifies against its own output; assumptions block composition

**Where.** `Gadget.lean:86-92` (`toModel`, `impl`), `Gadget.lean:106-113`
(`realizes`), `Functionality.lean:102-105` (`ofGadget`).

```lean
noncomputable def toModel (g : Gadget M I O) : Model (OpOf I O) L PMF where
  program o := match o with | .call i => Prod.fst <$> dist M (g.circ i)   -- the circuit's own output
  leak o x := match o with | .call i => g.view i x

theorem realizes (g : Gadget M I O) (kσ) (h : g.RealizesModel kσ) (hA : ∀ i, g.Assumptions i) :
    Realizes kσ (fun _ => ()) g.impl M g.toModel
```

**What it says.** A gadget becomes an abstract operation whose program is
"whatever the circuit computes" and whose leak is the declared view, and
its circuit realises that operation, provided the assumptions hold for
every input.

**Why that is wrong.**

(a) The program is self-derived. `Realizes toModel` says nothing against an
independent specification; DESIGN §7 and `Compose.lean:10` say
"program := its spec". Correctness lives only in the separate relational
`Spec`, which may be `fun _ _ => True`. A wrong inversion gadget with a
trivial `Spec` composes as happily as a right one.

(b) `hA : ∀ i, Assumptions i`. `invertGadget` has `Assumptions x := x ≠ 0`
over `I := F`, so `hA` would prove `0 ≠ 0`. The flagship gadget cannot be
turned into a functionality. The deeper reason is that a polymorphic caller
holds an opaque `x : D.S` and has no proposition about its value, so
Clean-style "discharge at the call site" does not transfer as stated at
DESIGN §7.

(c) A gadget carries two privacy obligations: `simulatable` (untagged) and
`RealizesModel` (tagged). `invertGadget` proves only the former, and the
comment at `Gadget.lean:96` ("enough for a top-level `Hiding`") is false:
`shapeLeak` packaged as a gadget with empty view passes `simulatable`.

**Options for (a).**

*Option 4A. A gadget is a `Realization` of an explicitly stated
functionality, plus an optional postcondition proved on the ideal side.*

```lean
-- sketch
structure Gadget (G : Functionality L) (I O : Type) where
  spec     : I → PMF O                       -- the ideal program, stated independently
  declared : I → O → List L                  -- the disclosure policy (trusted, by design)
  Pre      : I → Prop
  circ     : I → Circ G.ops O
  realizes : ∃ Sim : List L → PMF (List (G.K × List L)), ∀ i, Pre i →
    dist (G.model.tagged G.kind) (circ i) = do
      let y ← spec i
      let s ← Sim (declared i y)
      pure (y, s)
  Post     : I → O → Prop := fun _ _ => True
  post     : ∀ i, Pre i → ∀ y ∈ (spec i).support, Post i y   -- about spec, proved once
```

Output correctness of the circuit is inside `realizes` (the joint equation
forces the output marginal to equal `spec i`). `Post` is a convenience
derived from `spec`, never re-proved against the implementation.

*Option 4B. Minimal patch.* Keep `Gadget`, add a `spec : I → PMF O` field,
require `correct_dist : ∀ i, Assumptions i → Prod.fst <$> dist M (circ i) = spec i`,
and let `toModel.program := spec`. Delete `simulatable`, keep
`RealizesModel`.

**Options for (b).**

*Option 4C. Conditional realisation with a validity judgment (default).*
Preconditions are on requests; the caller proves, at the ideal domain, that
every request it issues on the support of its run satisfies them. This is
structural recursion on the free monad restricted to supported responses.

```lean
-- sketch
def Valid (M : Model τ L PMF) (Pre : {β : Type} → τ β → Prop) : Circ τ α → Prop
  | .pure _   => True
  | .call o k => Pre o ∧ ∀ y ∈ (M.program o).support, Valid M Pre (k y)

theorem handle_realizes_valid
    (Sim : Kτ → List L → PMF (List (Kσ × List L)))
    (h : ∀ {β} (o : τ β), Pre o →
      dist (Mσ.tagged kσ) (impl o) = do
        let y ← Mτ.program o
        let s ← Sim (kτ o) (Mτ.leak o y)
        pure (y, s))
    (c : Circ τ α) (hc : Valid Mτ Pre c) :
    dist (Mσ.tagged kσ) (Circ.handle impl c) = do
      let r ← dist (Mτ.tagged kτ) c
      let s ← simList Sim r.2
      pure (r.1, s)
-- proof shape: as handle_realizes; at `call` use hc.1 for the local equation and
-- hc.2 with PMF.bind_congr_support (Cost.lean:69) for the continuation.
```

Example of discharge: a caller that inverts only the output of `randNZ`
proves `Valid` because the support of `RandNZ.ideal` is the nonzero
elements. Nested realisations additionally need `Valid` of each intermediate
implementation for the lower layer's preconditions.

*Option 4D. Subtype requests.* `OpOf {i // Pre i} O`. Works when the
precondition is about clear data; for shares the caller cannot build the
proof (see above), so this is a special case, not the general mechanism.

*Option 4E. Totalise.* Give the functionality a defined behaviour on bad
inputs and declare the leakage honestly. For inversion by masking:
`invert 0` returns `0` (Lean's `0⁻¹ = 0`) and the opened value is always
`0`, so the honest total contract discloses whether `x = 0`.

```lean
-- sketch: a second, separately named functionality
def InvTotal.ideal : Model (Inv (.ideal F)) F PMF where
  program o := match o with | .inv x => pure x⁻¹
  leak o _  := match o with | .inv x => [if x = 0 then 1 else 0]   -- zero status
```

This is a *different* contract from "inversion, no leak, nonzero input";
both may exist under different names. It must not silently replace the
first.

**Recommendation.** 4A for structure, 4C as the default assumption
mechanism, 4E as a named alternative where natural.

**Decision (2026-09-05): functionalities all the way (Section 4, Option G1,
not G3).**

1. **Specifications are functionalities.** A functionality is an interface
   (operations, operand types, response shape; Issue 2) with one joint
   ideal `step` at the ideal domain (Issue 5; `program` and `leak` are
   its marginals). The functionality may look inside its
   operands (it is the trusted party); a program in the hybrid may not
   (Issue 3). Example: `AES` takes `⟦k⟧ ⟦v⟧`, computes `aes k v`, returns
   `⟦o⟧`, leaks nothing.
2. **A realisation is a program plus a simulator plus the proof.**
   `Realization F G` gives, for every operation of `F` and every domain, a
   program over `G`; a simulator `Sim : Event F → PMF (List (Event G))`; and
   the equation "the program's (response, view) equals `F`'s response paired
   with `Sim` of `F`'s event". Perfect: equality of distributions;
   statistical: TV ≤ ε with exact output marginal (Issue 6).
3. **`Gadget` is removed**, with `toModel`, `simulatable`, `RealizesModel`,
   `Hiding`, `Hiding.transport`. "This program is private with leakage `L`"
   is `Realization (ofOp spec L) G` for a one-operation functionality; a
   gadget is that, and at most an `abbrev`. Relational postconditions
   (`y · x = 1`) are lemmas about `F.program`, proved once, transported by
   `output_transport`. Cost stays outside (decision 005).
4. **Assumptions belong to realisations, not functionalities.** A
   functionality is total. "`invert` needs `x ≠ 0`" is stated in one of two
   honest ways, both allowed to coexist under different names: a total
   functionality whose `program`/`leak` say what happens on bad input
   (`inv 0 = 0`, leak `[x = 0]`; abort once an abort response exists), or a
   realisation with `Pre` proved only for valid requests, discharged by the
   caller through `Valid` on the support of its run at the ideal domain
   (Issue 4, Option 4C). The caller chooses: prove `Valid` for the silent
   contract, or use the total one and pay the declared leakage. Subtype
   requests (4D) only for preconditions on clear data.
5. **Composition is `Realization.comp`, once.** Inlining composes programs,
   `simList` composes simulators, and `Valid` obligations pass to the layer
   below. `AesHybrid.lean` is already in this shape and is the template;
   the trusted base is the identity realisations, i.e. the MPC's price list.
6. **A program in a hybrid has semantics regardless of how the hybrid's
   functionalities are instantiated** (author, 2026-09-05; decision 013
   made literal). A hybrid is a **list** of functionalities; its model is
   assembled from the components' ideal models and nothing else, so a
   program's meaning is fixed the moment it typechecks. Instantiation
   (`Realization.comp`) never changes that meaning: it yields a *different*
   program over the target hybrid (the one containing the dependencies the
   replacement uses; inlining need not shorten the list), and the
   composition theorem relates the two runs. Proving `A1 : Realization F1 fs` with
   `[Has F2 fs]` uses `F2.model`, the specification, never an
   implementation of `F2`.
   ```lean
   abbrev Hybrid := List Functionality
   def Hybrid.ops   fs := ⟨(i : Fin fs.length) × (fs.get i).ops.Op, fun ⟨i,o⟩ => (fs.get i).ops.dom o, fun ⟨i,o⟩ => (fs.get i).ops.cod o⟩
   def Hybrid.model fs := { step | ⟨⟨i,o⟩, a⟩ => (fs.get i).model.step ⟨o,a⟩ }   -- dispatch, definitional (sketch shows program/leak)
   class Has (F : Functionality) (fs : Hybrid) where i : Fin fs.length; eq : fs.get i = F   -- the whole certificate
   -- instances here/there walk the list, as Features.lean:49 does today
   ```
   **`Has` is the cleanest certificate: one equality of functionalities**,
   from which operands, response, program and leak transport at once. No
   injection, no `dom_eq`/`cod_eq`, no `program_eq`/`leak_eq`, no
   `Model.sum`; the five-field `Incl` structure first drafted (scratchpad
   `HasF.lean`) is superseded. Generic theorems need no law:
   `output_op [Has F fs] r : output fs.model (Prog.op r) = F.model.program r`
   is `obtain ⟨i, e⟩ := h; subst e; rfl`, and
   `mul3_correct (fs) [Has Mult fs] : output fs.model (mul3 a b c) = a*b*c`
   holds for every hybrid containing `Mult`, wherever it sits; concrete
   hybrids (`[Lin, Mult]`, `[Mult, Lin]`) close by `rfl`. Checked in core
   Lean 4.29 (scratchpad `Hyb.lean`).
   **Two relations, two roles.** `Has F fs` is structural: `F` is a black
   box available in the hybrid; programs are typed against it and their
   semantics uses `F.model`. `Realization F G` is semantic: `F` can be
   implemented over `G` with a simulator; instantiation consumes it. The
   only bridge is the trivial realisation (calling `F` realises `F` over any
   hybrid containing it), which is the trusted base.
   **Price lists unify.** `MPC := List ((F : Functionality) × (F.ops.Op → Price))`:
   prices are per operation (constant pricing is the special case), looked
   up at the same position `Has` finds; the same list gives membership,
   semantics and pricing, so the three unconnected ways of saying "the MPC
   offers X" (`Has τ σ`, `FS.Has`, `MF.Has`; finding A10) become one, and
   the `Feature`/`Cap` enumerations go. Not yet specified: the policy for
   duplicate entries (two occurrences of one functionality have the same
   meaning but different positions and possibly prices; instance search
   takes the first) and reindexing under reordering. Principle recorded: whoever writes a
   functionality, base primitive or sub-library, is responsible for its
   being reasonable; the framework guarantees that programs cannot
   circumvent it.

### Issue 5. Deterministic `leak` cannot express a random disclosure; the `randomCombination` claim is false

**Where.** `Model`, `Glean.lean:188`; DESIGN §6.3 line 1329 ("hiding is
immediate: the simulator draws its own coin"); `randomCombination`,
`Glean.lean:725`.

**What the prose says.** A random linear combination with a public coin is
hiding because the simulator can draw the coin itself.

**Why that is false.** The output share is `r · x` and the view is `[r]`.
They are correlated. Over `ZMod 2` on the single input `[x]`:

| input | output | view | probability |
|-------|--------|------|-------------|
| x = 0 | 0 | [0] | 1/2 |
| x = 0 | 0 | [1] | 1/2 |
| x = 1 | 0 | [0] | 1/2 |
| x = 1 | 1 | [1] | 1/2 |

`Hiding` needs one `Sim` with `Sim 0` uniform (from `x = 0`) and
`Sim 0 = pure [0]` (from `x = 1`). No such `Sim`. The joint definition is
right to reject this: if a caller later opens the result, the adversary
learns both `Σ rⁱ xᵢ` and `r`, so the honest specification of the operation
is a *joint law* of (challenge, result), not "leaks nothing".

**The expressiveness gap this exposes.** Try to state that honest
specification as a one-operation functionality: program
`xs ↦ Σ rⁱ xᵢ` with `r` drawn, disclosure `[r]`. `Model.leak : σ β → β →
List L` is deterministic given request and response, and the response does
not determine `r` (all-zero `xs`: result `0`, `r` uniform). It cannot be
written. Any randomised gadget whose public disclosure is not recoverable
from its response has the same problem.

**Options.**

*Option 5A. Joint ideal step.* Replace the pair (program, leak) by one
distribution over (response, disclosure).

```lean
-- sketch
structure Model (σ : Sig) (L : Type) (m : Type → Type) where
  step : {α : Type} → σ α → m (α × List L)

def Model.ofDet (program : {α : Type} → σ α → α) (leak : {α : Type} → σ α → α → List L) : Model σ L m :=
  ⟨fun o => pure (program o, leak o (program o))⟩          -- every existing deterministic model

def run … : Circ σ α → m (α × Trace C L)
  | .pure a   => pure (a, Trace.zero)
  | .call o k => do
    let (x, l) ← M.step o
    let r ← run M K (k x)
    pure (r.1, Trace.seq ⟨K.op o, l⟩ r.2)

def Model.tagged (M : Model τ L m) (kind) : Model τ (K × List L) m :=
  ⟨fun o => do let (y, l) ← M.step o; pure (y, [(kind o, l)])⟩

def Realizes … : Prop :=
  ∃ Sim, ∀ {β} (o : τ β),
    dist (Mσ.tagged kσ) (impl o) = do
      let (y, l) ← Mτ.step o
      let s ← Sim (kτ o) l
      pure (y, s)
```

`run_bind`, `dist_bind`, `dist_call`, `handle_realizes` keep their shape;
the induction is the same. `randomCombination` then has the functionality
`step xs := do let r ← uniform F; pure (Σ rⁱ xᵢ, [r])`, and its circuit
realises it with the simulator that replays `r`.

*Option 5B. Return the public value.* Change the interface so the response
carries the disclosure: `rc : List D.S → RandComb D (D.F × D.S)` with
`leak _ y := [y.1]`. Natural for this example (callers often need `r`), but
every random disclosure must then be returned, which changes caller-visible
interfaces and every handler.

*Option 5C. Document the limitation.* State that one-op functionalities
with random disclosures not determined by the response are out of scope.
Not recommended; the class includes public-coin protocols in general.

**Recommendation.** 5A. Mechanical, and it removes the only place where the
core cannot say what a real functionality does.

**Decision (2026-09-05).** Option 5A. The ideal step samples response and
disclosure together, `step : Req → m (Resp × List Pub)`; `step` is the
authoritative joint law, `program` is its response marginal, and there is
no deterministic `leak r y` accessor (marginals cannot recover the
correlation). Constructors embed old models: deterministic ones as
`pure (program r, leak r (program r))`, randomised ones as
`do y ← program r; pure (y, leak r y)`. The interpreter records the
*sampled* disclosure in the event; the simulator receives (operation,
clear outputs, sampled disclosure); the continuation receives the same
sampled response. `run_bind` unchanged; `handle_realizes` samples the joint
event before the continuation. `randomCombination`'s spec becomes "returns
`⟦Σ rⁱxᵢ⟧`, discloses `r`" without returning `r`. Option 5B (the coin as a
clear output component) remains an interface choice when callers should
receive it; it cannot express a disclosure no honest party receives. With
hybrids as lists (Issue 4 item 6), `step` sits in `Functionality.model` and
`Hybrid.model` dispatches it unchanged. Recommended by both reviewers.

### Issue 6. `RealizesStat` permits output error; the composition lemma is missing

**Where.** `RealizesStat`, `Privacy.lean:122`; `HidingStat`,
`Glean.lean:490`; DESIGN §8 item 1; decision 009.

**What it says.** Within `ε` in total variation, the joint (response, view)
of the implementation matches the abstract response with a simulated view.

**Why that is wrong.** The bound is on the joint, so the response may be
wrong with probability up to `ε`, contradicting decision 011 ("correctness is
perfect") and making a statistical `output_transport` impossible.

```lean
-- Rand over ZMod 2 realised by a constant, honest Std.ideal:
--   impl .rand := const 0           concrete: pure (0, [(0, [])])
--   Sim _ _   := pure [(0, [])]     ideal:    do y ← uniform (ZMod 2); pure (y, [(0, [])])
-- statDist = 1/2, so RealizesStat … (1/2) holds; the output is wrong half the time.
```

Nothing composes yet: no lemma relates `statDist` and `bind`. Two traps for
when it is written. The number of calls a reactive caller makes is a random
variable, and the worst case over paths may be infinite. And one must not
condition on the final call count and then treat the coins as still jointly
uniform; `seqUniform_eq_uniform` is for a fixed number of draws.

**Options.**

*Option 6A. Keep perfect correctness: exact output marginal plus TV on the
joint (output, view).*

```lean
-- sketch
structure RealizesStat (kσ) (kτ) (ε : ENNReal) (impl) (Mσ) (Mτ) : Prop where
  output_eq  : ∀ {β} (o : τ β), Prod.fst <$> dist Mσ (impl o) = Mτ.program o
  simulation : ∃ Sim, ∀ {β} (o : τ β),
    PMF.statDist (dist (Mσ.tagged kσ) (impl o))
      (do let y ← Mτ.program o; let s ← Sim (kτ o) (Mτ.leak o y); pure (y, s)) ≤ ε
```

*Option 6B. Coupling-based definition* with almost-sure equality of
responses. Equivalent strength, better proof infrastructure, more setup.

*Option 6C. Accept output error* under a separate name, with an
`output_transport` that only bounds TV.

The lemma needed in all cases, provable with the existing `ENNReal` `tsum`
representation and no measure theory:

```lean
-- sketch
theorem PMF.statDist_bind_le {A B : Type} (p q : PMF A) (f g : A → PMF B) :
    PMF.statDist (p.bind f) (q.bind g) ≤
      PMF.statDist p q + ∑' a, q a * PMF.statDist (f a) (g a)
-- via q.bind f in the middle: triangle; contraction for a common kernel; weighted mixture bound.

-- caller budget, by induction on the free monad:
--   B (pure a)   = 0
--   B (call o k) = ε o + ∑' y, Mτ.program o y * B (k y)
--   statDist (concrete caller) (simulated abstract caller) ≤ min 1 (B c)
-- constant ε gives min 1 (ε · E_ideal[number of calls]); a finite worst-case bound is a special case.
```

**Recommendation.** 6A, which matches the declared contract; the lemma and
the budget theorem as the first piece of statistical work.

**Decision (2026-09-05).** Option 6A, stated on the **joint**: exact
output marginal, and total variation between the real and simulated joint
(output, view) distributions ≤ ε. Not TV on the view alone: over `F₂`,
`b ← rand; t ← add x b; reveal t; pure b` has uniform output and uniform
disclosure for every `x`, so an independent-coin simulator passes marginal
TV with ε = 0 while the joint has TV ½ and a caller opening `b` learns `x`
(GPT round 4). Kernel lemma `statDist_bind_le` as stated above; caller
budget `B(pure) = 0`, `B(call r k) = ε(r.op) + E_{y ← response} B(k y)`,
bound `min 1 (B c)`, expectations over the ideal execution in `ENNReal`;
nested realisations add the inner expected budget. New proof work, not
migration (decision 009 left it open).

### Issue 7. Leaf proofs are untagged; the composition theorem needs tagged

**Where.** `Hiding.transport`, `Compose.lean:83`, consumes
`Hiding (Mτ.tagged kτ) P`.

| Proof | Model | Usable by `Hiding.transport` |
|-------|-------|------------------------------|
| `beaver_hiding` (Glean.lean:873) | untagged | no; but `dist_beaver` + `preHandler_realizes` (Privacy.lean:177, 198) give the tagged form |
| `mulBeaver_hiding`, `mul3Beaver_hiding` (Beaver.lean) | untagged | no |
| `b2a_hiding` (MultiField.lean:401) | untagged | no |
| `invertGadget.simulatable` (Gadget.lean:157) | untagged | no; `RealizesModel` not proved |
| `Arith.hiding` (Silent.lean:86) | untagged | no |
| `cbc2Hybrid_hiding`, `cbc2Plain_hiding` (AesHybrid.lean) | tagged | yes |

There is no bridge from untagged to tagged, and `shapeLeak` (Issue 3) shows
the general implication is false, not merely unproved. DESIGN §4.1 line
1043 ("every circuit proved hiding on the arithmetic black box is hiding on
the preprocessing functionality ... with no new proof") is therefore too
broad: only tagged statements transport.

**Options.** Prove leaf results directly as tagged realisations (the cost
is the same: `preHandler_realizes`, `sqRevCircuit_realizes`,
`toyAes_realizes`, `cbc_realizes_hybrid` already are), and retire the
untagged `Hiding`. Or keep untagged results as explicitly weaker
corollaries derived from the tagged ones. A general bridge lemma for
straight-line circuits is possible ("if every run has the same list of
kinds and per-record leak lengths, the tagged view is a function of the
untagged one") but is more work than restating the six proofs.

**Recommendation.** Restate as tagged; delete `Gadget.simulatable`.

**Decision (2026-09-05).** A consequence of Issues 1-4, confirmed: the six
untagged `Hiding` proofs (`beaver_hiding`, `mulBeaver_hiding`,
`mul3Beaver_hiding`, `b2a_hiding`, `invertGadget.simulatable`,
`Arith.hiding`) are restated as realisations of one-operation
functionalities with `leak := []`; `preHandler_realizes`,
`toyAes_realizes`, `sqRevCircuit_realizes`, `cbc_realizes_hybrid` are
already in that shape. `Arith.hiding` gets a public-trace hypothesis. No
bridge lemma is written; none is needed.

### Issue 8. Public inputs have no slot; clear request payloads are invisible

**Where.** `Hiding` quantifies over all of `I` as secret; `Lin.ideal.leak
(const c) _ := []` (`Glean.lean:534`); `Std.kind` merges `Lin` ops.

**Why that is wrong, both ways.**

Too weak: `c` in `const c` or `smul c x` is public in a real ABB (all
parties apply it), but the modelled view does not contain it. If a circuit
takes a private clear value and calls `const` on it, the leak is not seen:

```lean
def broadcast (c : F) : Circ (Std (.ideal F)) Unit := do let _ ← const (D := .ideal F) c; pure ()
-- view: untagged [], tagged [(0, [])], for every c.  Hiding with Sim _ := pure [].
```

Too strong: legitimately public inputs (list lengths, the sorted table in
`binarySearch`) determine the trace shape. With `I := Nat × F` and a
circuit doing `n` silent additions, tagged `Hiding` fails because the
simulator is not told `n`, even though `n` is public.

**Fix.** Both symptoms come from erasing the public/secret distinction on
inputs. Issue 1A's `pubIn` gives the simulator public inputs; Issue 2A's
kinds carry clear payloads. Do not fix the second by widening `kind` to
"the whole request", which is Issue 2's hole again.

**Decision (2026-09-05).** A consequence of Issue 2, confirmed: a
program's public inputs are the clear payload of its one-operation
functionality's operation, its secret inputs are the operands, the same
split as everywhere else. `const c` and `smul c` carry `c` in the operation
header. Nothing further.

### Issue 9. Prose contradicts code

| Location | Says | Should say |
|----------|------|------------|
| DESIGN.md:45-52 (§1) | the view is the list of opened values | the view is the tagged trace (§4.1, decision 012) |
| DESIGN.md:915 | "the simulator's independence from the output is what `bind` means" | delete; `Sim y` depends on `y`. Fresh `bind` gives fresh coins, not independence from the output |
| DESIGN.md:1060-1071 | non-transitivity example: `Z` a coin, `Y = ()`, `X = Z` | that example *is* transitive (`Sim z := pure z`). Correct example: secret `i : ZMod 2`, fresh uniform `Z`, `Y := ()`, `X := i + Z`; "X given Y" (uniform) and "Y given Z" (trivial) hold, "X given Z" needs `Sim z = pure z` for `i = 0` and `pure (z + 1)` for `i = 1` |
| DESIGN.md:1043 | every circuit proved hiding on the ABB transports | only tagged statements transport |
| DESIGN.md:1329 | `randomCombination` is hiding | it is not (Issue 5); its spec is a joint law |
| DESIGN.md:655 | models carry no state, "that is what makes `run_bind` hold in every lawful monad" | `run_bind` holds with state too (it is used at `Sched := StateT Clock Id`); statelessness is what makes the per-call `Realizes` equation compose (`PMF.bind_comm` in `handle_realizes`) |
| DESIGN.md:527 | perfect hybrid + computational base gives computational security | conditional on an efficient simulator (Sim is an arbitrary `PMF` kernel here) and an interactive embedding; both are outside the framework |
| DESIGN.md:1485 (§7) | callers discharge assumptions at the call site | not implemented (Issue 4b) |
| DESIGN.md:7, README.md:13 | compositional theorems are `sorry` | none are (decision 008 is correct) |
| DESIGN.md:128, 172, 191, 343 | `par` constructor, `Circ.parMap` | removed (decision 002 revisited); code uses `mapM` |
| DESIGN.md:105 | `inductive Get … | get : MulTriple D …` | `Get` is gone (decision 013); garbled |
| DESIGN.md:260, 292 | `MPC.cost : Option Nat` | `WithTop Price` |
| DESIGN.md:449 | `Functionality (L R : Type)` | `Functionality (L : Type)` with `K`, `kind` |
| DESIGN.md:1124 | `cost M ⟨.rounds, κ⟩` | no such cost model; delay is the timed domain |
| DESIGN.md:62 | `Gadget` bundles a round bound | it does not (decision 005) |
| decisions/006:30 | `handle_private` | `handle_realizes` |
| decisions/005:5 | "good coins" | removed by 009/011 |
| decisions/012:18 | simulator "never [sees] the request's payload" | not enforced (Issue 2) |
| Gadget.lean:96 | `simulatable` is "enough for a top-level `Hiding`" | false (Issue 4c) |

**Decision (2026-09-05).** The table is the list of prose edits; they are
applied together with the definitions, and where a "should say" entry
predates a later decision (adding `K`/`kind` to `Functionality`; "only
tagged statements transport") the final design wins: no `kind`, and
"only realisations over structural events transport".

### Issue 10. Delay does not compose exactly with timing profiles (outside the privacy focus)

**Where.** DESIGN §3.4 lines 783-802; `Cost.lean:17-20`;
`Timing.lean:127 profiled_handle_exact : True := trivial`.

**What it says.** Under dependency tracking, modelling an abstract
operation by its input-to-output delay profile makes the caller's round
count equal to the inlined circuit's.

**Why that is false as stated.** The timed interpreter has global state:
the reveal clock and the control clock (`Glean.lean:363`). `const` and
`smul` are timed at `max (…, s.revealed)`, so an inlined callee that does
"reveal, compute in the clear, insert back" waits on every earlier reveal in
the *caller*, which no per-op profile of the callee can know. Two
independent reactive sub-circuits placed in sequence also interfere by
program order. A profile therefore gives an upper bound for reactive
callees; only a full clock-state transformer per abstract operation
composes exactly.

**Fix.** Downgrade the claim; keep the placeholder theorem but label it as
such; or specify abstract operations by their clock-state transformer.

---

**Decision (2026-09-05).** Option 10A: downgrade the claim. Timing
profiles are a **conservative bound requiring a stated clock-aware
hypothesis and proof**, not an established consequence: the reveal and
control clocks are global state, so even a straight-line callee such as
`smul 1 x` after an earlier reveal at time `T` returns at `T` while its
isolated profile is zero (Glean.lean:394). `Timing.lean:127` is labelled a
placeholder. Option 10B (an abstract operation's timing as its full
clock-state transformer) is recorded for when an exact number is needed.
Delay is a cost, not a privacy property; the `barrier` discipline stays
(restored in the sketch, revision 2, with the control clock; GPT's
reveal-then-branch program reports 3 rounds with it, 1 without). The
timed model's `pubArg`/`ctrl` flags are trusted scheduling metadata; a
revealed branch that selects an existing share with `pure` still escapes
the control time (known gap).

## Scope decisions (2026-09-05)

- **Computational security (DESIGN §2.11:527) is a prose fix.** The
  framework proves the perfect hybrid step; the transfer to a
  computationally secure base needs an efficient simulator and an
  interactive embedding, both outside the framework. State it as a
  conditional external application, not a consequence of
  `Realization.comp`. No efficiency certificate for simulators is planned.
- **Migration order.** Prototype first: one multiplication realisation
  (Beaver over `[Lin, Reveal, MulTriple]`) and one mixed-field program on
  the new core, with `Valid`, `handle_realizes_valid` and the statistical
  kernel lemma stated before the full rewrite of the sketch.
- **Name.** "Glean" collides with Meta's code-index tool and Mozilla's
  telemetry SDK; the repository is already `weft`. Left to the author.

- **Functionalities stay stateless for the foreseeable future** (author).
  The `PMF` realisation layer models fresh, per-request calls; hidden
  persistent state across calls, interleaved sessions, batched MAC checks
  and amortised preprocessing are out of scope. Stateful functionalities
  are noted as a possible future extension, not planned. Response-dependent
  callers are already supported and are not what this excludes.

## 3. Three ways to act on this (pre-decision options, kept as history; see Section 5 for what was decided)

**Package 1: patch.** Issues 1A, 2A, 6A, 7, 9. Every existing proof
adapts by adding `()` projections and restating six leaf theorems as
realisations. The structure of the design is unchanged. Removes the two
high-severity vacuity routes.

**Package 2: restructure around `Realization`.** Package 1 plus 4A, 4C,
5A, 3A, 3B. The design then has one privacy notion (a realisation of an
explicitly stated functionality), one observation model (the tagged trace
with canonical field-indexed kinds), joint ideal steps, conditional
composition for assumptions, and privacy statements that quantify over the
domain. DESIGN §2.10's "one notion" becomes literally true. This is the
version worth writing the next decision records for.

**Package 3: enforce.** Package 2 plus 3C (checked front-end) and an
efficiency certificate for simulators (a computable sampler with a runtime
bound, plus the interactive embedding theorem DESIGN §2.11 alludes to).
Only worth it once the library is large.

Suggested order inside Package 2: 2A and 1A first (they fix the definitions
that can be satisfied vacuously); 5A next (it changes `Model`, so do it
before more models are written); 4A/4C; 6A with the `bind` lemma; 7 and 9
throughout.

Suggested new decision records: 014 "Public observations are explicit and
never automatic" (Issues 1, 2, 3, 8); 015 "One certificate: tagged
realisation of an explicit functionality" (Issues 4, 5, 6, 7).

---

## 4. Should gadgets and functionalities be distinct notions?

Today they are two parallel structures with two sets of obligations, and
decision 006 says a gadget "is" a one-operation functionality plus
assumptions. Issue 4 shows the parallel structures drifted: `Gadget` proves
privacy twice (untagged and tagged), certifies against its own output, and
cannot be composed when it has assumptions. So the question is real.

**What the two words mean, and what each is for.**

| | Functionality | Gadget |
|---|---|---|
| Role | An *interface with a meaning*: what a caller programs against; the unit of trust (`Realization.id`) and of pricing | An *implementation artefact*: a specific circuit with what it needs and what it guarantees, the way Clean's `FormalCircuit` is |
| Shape | Any number of operations (`Std` has three); total on every request; one canonical meaning per name (decision 013) | One operation; typically partial (`x ≠ 0`); may want a *relational* postcondition rather than a distribution |
| Author | Protocol designers, the library (the trusted base) | Library authors writing sub-circuits |
| Composition | Through `Realization.comp`/`sum` and `handle_realizes` | Today: through `toModel`, which is where it breaks |

The distinction that is worth keeping is the *role* distinction. The one
that is not worth keeping is the *mechanism* distinction: two structures,
two privacy obligations, two ways of turning a circuit into something a
caller can use.

**Option G1. Collapse completely.** Delete `Gadget`. A verified sub-circuit
is `Realization (Functionality.ofOp spec declared) G`; assumptions are the
conditional realisation of Option 4C; a relational postcondition is a
separate lemma about `spec`. Simplest theory; loses the ergonomic bundle
that Clean users expect, and every small gadget must name an explicit
distribution even when a relation would have done.

**Option G2. Keep both as now, fix the fields.** Add `spec` to `Gadget`,
require `correct_dist`, delete `simulatable`. Least churn; keeps two notions
with overlapping obligations, and the "which one do I use" question stays.

**Option G3. Gadget as a derived notion (recommended).** One mechanism,
two names. A gadget is *defined as* a conditional realisation of a
one-operation functionality, with an optional relational postcondition
proved once on the ideal side:

```lean
-- sketch
/-- A one-operation functionality from an ideal program and a disclosure policy. -/
def Functionality.ofOp (spec : I → PMF O) (declared : I → O → List L) : Functionality L :=
  ⟨OpOf I O, fun _ => Unit, fun _ _ => (), { step := fun | .call i => do let y ← spec i; pure (y, declared i y) }⟩

/-- A realisation that is only promised on requests satisfying `Pre`. -/
structure Realization (F G : Functionality L) where
  impl     : {β : Type} → F.ops β → Circ G.ops β
  Pre      : {β : Type} → F.ops β → Prop := fun _ => True
  realizes : RealizesOn Pre G.kind F.kind impl G.model F.model      -- ∀ o, Pre o → …

/-- A gadget: the realisation of its own one-op functionality, plus what a caller may
conclude about the ideal output without unfolding anything. -/
structure Gadget (G : Functionality L) (I O : Type) where
  spec     : I → PMF O
  declared : I → O → List L
  Pre      : I → Prop
  circ     : I → Circ G.ops O
  real     : Realization (Functionality.ofOp spec declared) G   -- impl := fun | .call i => circ i,  Pre := fun | .call i => Pre i
  Post     : I → O → Prop := fun _ _ => True
  post     : ∀ i, Pre i → ∀ y ∈ (spec i).support, Post i y
```

What this keeps: the Clean ergonomics (`Pre`, `Post`, a circuit, one
bundle); the UC semantics (an explicit `spec` and `declared`, so the
certificate says something independent of the implementation); a single
composition theorem (`handle_realizes_valid`), since `Gadget.real` is a
`Realization`; cost, which was never part of the gadget (decision 005) and
still is not.

What it changes: a gadget must name its ideal output distribution. For a
deterministic gadget that is `pure (f i)`; for a randomised one (`randNZ`,
`randomCombination`) it is the honest joint law, which is exactly what
Issue 5 says must be expressible. A gadget with only a relational spec and
no natural distribution cannot take part in privacy composition anyway
(callers' continuations depend on its output distribution), so requiring
`spec` loses nothing that was sound.

What stays distinct: a `Functionality` may have many operations, is total,
and is what the trusted base and the price list are made of; a `Gadget` is
one operation, may be partial, and is how a library author packages a
sub-circuit. `Functionality.sum` and `Realization.sum` assemble the former
from the latter.

**Recommendation.** G3. It answers the question "yes, distinct, but the
gadget is a *pattern over* the functionality notion, not a second theory",
which is what decision 006 already wanted to say and the code did not do.

**Decision (2026-09-05).** G1, going one step further than the
recommendation: functionalities all the way, `Gadget` removed, "gadget" at
most a word for a one-operation realisation. See the decision under Issue 4.

---

## Final design (authoritative; issue sections and Sections 3-4 are history)

Schematic signatures; implicit arguments and universes omitted. Sketches:
`Design.lean` (revision 2: events, interfaces, Beaver, two clear types,
timed model; still uses sums, obsolete) and `Hyb.lean` (list hybrids and
`Has`; still has sorts, obsolete). Neither combines every final choice;
this section does.

```lean
-- Domains: a share of a T, interpreted per domain.  Programs are polymorphic in D.
structure Domain where sh : Type → Type
def ideal  : Domain := ⟨fun T => T⟩           def erased : Domain := ⟨fun _ => Unit⟩

-- Response shapes (closed language; lists, Option/sums and clear-indexed dependent pairs to be added).
inductive Shape | unit | clear (T : Type) | share (T : Type) | prod (a b : Shape) | vec (n : Nat) (a : Shape)
-- interp D : Shape → Type;  blank : interp D sh → interp erased sh   (clear kept, share ↦ ())

-- An interface: public operations (constructor + clear arguments), operand types, response shape.
structure Interface where Op : Type; dom : Op → List Type; cod : Op → Shape
structure Req (ι) (D) where op : ι.Op; args : Operands D (ι.dom op)          -- operands: shares only
abbrev Resp ι D o := (ι.cod o).interp D

-- The adversary's record of one request: operation, clear outputs, declared disclosure.
def Event ι := (o : ι.Op) × Resp ι erased o × List Pub                        -- Pub: encoding policy to be fixed

-- A model: one joint ideal step per request.  `program r := Prod.fst <$> step r`; no `leak r y` accessor.
structure Model (ι) (D) (m) where step : (r : Req ι D) → m (Resp ι D r.op × List Pub)

-- A functionality: interface with meaning.  Total.  Written by a trusted author.
structure Functionality where ops : Interface; model : Model ops ideal PMF

-- A hybrid: a list of functionalities.  Its interface indexes the list; its model dispatches by position.
abbrev Hybrid := List Functionality
-- fs.ops.Op := (i : Fin fs.length) × (fs.get i).ops.Op ;  fs.model.step ⟨⟨i,o⟩,a⟩ := (fs.get i).model.step ⟨o,a⟩
class Has (F : Functionality) (fs : Hybrid) where i : Fin fs.length; eq : fs.get i = F   -- the certificate
-- instances here/there walk the list; Prog.op transports opAt along eq; generic theorems by subst.

-- Programs (not circuits): the free monad; branch on public values; polymorphic in D.
inductive Prog (ι) (D) : Type → Type 1 | pure : α → Prog ι D α | call (r : Req ι D) : (Resp ι D r.op → Prog ι D α) → Prog ι D α
-- run samples step once per call, records ⟨r.op, blank y, ℓ⟩, continues with y.  dist := run at PMF.

-- A realisation: a program for every domain, a simulator, the equation; a precondition where the guarantee holds.
structure Realization (F : Functionality) (fs : Hybrid) where
  impl : (D : Domain) → (r : Req F.ops D) → Prog fs.ops D (Resp F.ops D r.op)
  Pre  : Req F.ops ideal → Prop := fun _ => True
  Sim  : Event F.ops → PMF (List (Event fs.ops))
  real : ∀ r, Pre r → dist fs.model (impl ideal r) =
           do let (y, ℓ) ← F.model.step r; let s ← Sim ⟨r.op, blank y, ℓ⟩; pure (y, s)
-- Valid M P (pure _) := True ;  Valid M P (call r k) := P r ∧ ∀ z ∈ (M.step r).support, Valid M P (k z.1)
-- comp (f : Realization F fs) (g_i : Realization (fs.get i) gs) : Realization F gs
--   impl := inline ;  Sim := f.Sim then simList g_i.Sim ;  Pre r := f.Pre r ∧ Valid fs.model (dispatch g_i.Pre) (f.impl ideal r)
-- Untouched components of fs use the inclusion realisation given by Has.  No Hiding, no Gadget.
-- Statistical: exact output marginal and TV on the joint ≤ ε(op), under Pre; budget B(pure)=0,
--   B(call r k) = ε(r.op) + E_{y ← program r} B(k y); bound min 1 (B c).

-- Pricing: an MPC is the hybrid list with a per-operation price per entry.
abbrev MPC := List ((F : Functionality) × (F.ops.Op → Price))               -- constant pricing is a special case

-- Certificates: the `program` command builds Realization values; it checks the fully applied impl
--   (computable, domain-generic, no dependency inspecting shares), including composed terms.
-- Public inputs are operation payload; secret inputs are operands.  Sim's only runtime input is its event.
-- Functionalities are stateless PMF kernels; timed operational models keep the reveal/control clocks.
```

Not yet specified (recorded as open): the duplicate-entry and reindexing
policy for list hybrids and prices; the `Pub` alphabet and its encoding
requirements (old code used `Encodable`, MultiField.lean:131); the exact
mechanism by which the `program` command binds its check to the certified
`impl` and survives `comp`; the one-operation functionality constructor
with public payload, typed operands, response shape and joint step; the
timing contract (trusted `pubArg`/`ctrl`, random public control flow, the
`pure`-selection gap). Acceptance example before migration: a randomised
disclosure composed through a caller with a nontrivial precondition.

## 5. What changes, and why (consolidated)

Each row: what the design had, what it becomes, the reason, and who raised
it. Locations are in the current repository.

| Old | New | Why | Raised by |
|---|---|---|---|
| `Hiding` gives `Sim` the return value `y` (Glean.lean:482) | `Hiding` removed; top-level privacy is a `Realization` of a one-op functionality; `Sim` gets the event only; `(y, view)` stays in the joint | at the ideal domain a share is its value, so `do reveal x; pure x` is provably hiding; hidden components are not leaked until opened, clear ones are public at once, and a later opening must be consistent with the trace (`randomCombination` fails for this reason) | both reviewers; principle by the author |
| (amendment to this review's own first recording of Issue 1 item 3, not an old-repo feature: `Model.leak` already saw request and response, Glean.lean:191) declared disclosure restricted to clear data | `leak`/`declared` is the trusted specification and may depend on operands | "returns `[a·b]`, leaks `a − b`", "leaks the high bit" are ordinary functionalities; the restriction confused leakage with output | author (revision); Codex had argued it |
| `kind : {β} → τ β → K` chosen per theorem and per `Functionality` (Privacy.lean:113, Functionality.lean:30); `Std.kind` merges the four `Lin` ops | request = operation applied to share operands; the header *is* the operation; `Model.tagged`, `Functionality.K/kind` deleted | `payloadKind (mult x _) := x` certifies an implementation that opens `x`; the program is public so the header must show constructor and clear arguments, never shares | both reviewers; shape by the author's question |
| `leak : σ β → β → List L` as the only view channel; no mandatory recording of clear outputs (the honest `Reveal.ideal` records its output by hand, Glean.lean:543) | event = (operation, clear outputs, declared leakage); operation and clear outputs structural | a model could return an opened value and omit it from the view (`cod := clear F; leak := []`); clear outputs are public by the author's own principle | Codex round 3, author |
| `Sig : Type → Type u` GADTs (Glean.lean:25), single-field `Domain := ⟨F, S⟩`, multi-field `Domain.S : Type → Type` (MultiField.lean:28) | `Interface := (Op, dom : Op → List Type, cod : Op → Shape)`, `Domain.sh : Type → Type` for all, closed `Shape` language | structural blanking of responses needs a shape language; a share is a share (no sorts); the multi-field representation becomes the only one | Codex/GPT rounds 3-4; author on sorts |
| core `Has τ σ` on interfaces (Glean.lean:35), `Std`/`Pre` as sums (Glean.lean:161); fixed semantics existed only on the price-list route (`Feature.ideal`, Features.lean:115) | hybrid = `List Functionality`; `Has F fs := (i, fs.get i = F)`; model dispatches by position; prices per operation in the same list | core inclusion says nothing about meaning (decision 013's own remark); the five-field `Incl` with laws first drafted was superseded: one equality of functionalities is the whole certificate; extends the price-list guarantee to core typing | GPT round 4 (defect); author ("is this really the cleanest?") |
| `Hiding`/`Gadget.circ`/`Realization.impl` accept programs at the ideal domain | statements take `c : ∀ D, …`; `Realization.impl : (D : Domain) → …`; `program` command checks the fully applied term | `shapeLeak` branches on a share and is hiding; `Classical` lets even polymorphic definitions compare shares; Lean's `def` rejects that, a command must check applied terms and dictionaries | Codex round 2, GPT round 4; author kept the Lean DSL |
| `Gadget` with `toModel.program := own output` (Gadget.lean:86), `simulatable` + `RealizesModel` (Gadget.lean:41, 45 still give correctness and simulation obligations), `hA : ∀ i, Assumptions i` (Gadget.lean:106) | `Gadget` removed; specs are functionalities; realisation = program for every domain + simulator + equation; `Pre` on the realisation, discharged by `Valid` on the caller's run support (`invertGadget`'s `x ≠ 0` becomes such a `Pre`); total variants under their own names | the self-derived spec supplies no independent output-distribution specification; `invertGadget` could not compose; UC functionalities are total and a polymorphic caller cannot state `x ≠ 0` about a share | Codex round 1-2; author ("functionalities all the way") |
| `Model.leak` deterministic in (request, response) | `step : Req → m (Resp × List Pub)` is the authoritative joint law; `program` its response marginal; old models embed via constructors | `randomCombination` on all-zero input: response 0, coin uniform; no function of the response yields the coin; DESIGN:1329 claimed hiding, which is false | Codex round 2 |
| `RealizesStat` = TV on the joint, no output condition (Privacy.lean:122) | exact output marginal + TV on the **joint** | `Rand` by `pure 0` passes with ε = ½; view-marginal TV would pass `b ← rand; reveal (x+b); pure b` with ε = 0 while a later opening of `b` leaks `x` | Codex round 2, GPT round 4 |
| untagged leaf proofs (`beaver_hiding`, `mulBeaver_hiding`, `b2a_hiding`, `invertGadget.simulatable`, `Arith.hiding`) | restated as realisations with `leak := []`; `Arith.hiding` with a public-trace hypothesis | untagged → tagged is false in general (`shapeLeak`); `hiding_of_silent` ignores operation structure | both reviewers |
| `Circ`, "circuit" | `Prog`, "program"; "circuit" for the straight-line case; "protocol" for realisations | programs open values and branch on public values; "circuit" suggests straight-line | author |
| "delay composes exactly with profiles" (DESIGN §3.4, Cost.lean:17), `Timing.lean:127 : True` | a conservative bound under a clock-aware hypothesis still to be stated and proved; `Barrier` and control clock kept; `pubArg`/`ctrl` trusted metadata | reveal/control clocks are global state (even `smul 1 x` after a reveal at `T` returns at `T`); GPT's reveal-then-branch program undercounts (1 instead of 3) without the barrier | Claude, GPT rounds 4-5 |
| DESIGN §1, §4.1:915, §4.1:1060, §4.1:1043, §6.3:1329, §3.1:655, §2.11:527, README:13 and stale `par`/`parMap`/`Get`/`Option Nat`/`Functionality (L R)`/`⟨.rounds, κ⟩` | prose edits listed under Issue 9, with the final design winning where an entry predates it (no `K`/`kind`; "realisations over structural events transport") | contradict the code or are false (transitivity example; "bind means independence from the output"; "statelessness makes `run_bind` hold") | both reviewers |
| stateless ideal layer already (DESIGN.md:655, Functionality.lean:31), with stateful extensions implied by DESIGN §8 | stateless for the foreseeable future; stateful functionalities explicitly out of scope | batching, sessions and hidden state need a different realisation layer | author |
| computational transfer claimed as a consequence (DESIGN §2.11:527) | stated as a conditional external application | needs an efficient simulator and an interactive embedding the framework does not provide | GPT round 4 |
| no statistical composition (decision 009 open) | exact output marginal + joint TV; `statDist_bind_le`; expected-call budget `B` | `Rand` by `pure 0` and the masked-bit example (Issue 6) | Codex round 2, GPT round 4 |
| `Feature` (Features.lean:25) and `Cap` (MultiField.lean:67) closed enumerations, scalar `Price` per feature | prices per operation, `(F : Functionality) × (F.ops.Op → Price)` entries in the hybrid list | pricing by operation family with `const c` an operation per coefficient cannot be a finite list of pairs (Codex round 3) | Codex round 3, author |
| `Realization` values built by hand (`⟨impl, proof⟩`, Functionality.lean:148) | built only through the `program` command, which checks the fully applied `impl` | the check is part of the security argument once wiring is omitted from the view | GPT rounds 4-5 |

Superseded during the discussion and recorded in place: Issue 1 item 3
("clear data only", corrected to "trusted specification"); Issue 4 item 6
(five-field `Incl` with model laws, `HasF.lean`, replaced by the list
hybrid with one equality, `Hyb.lean`); Section 4's recommendation G3,
replaced by the decision G1; Section 3's "three packages", which were the
pre-decision options and are kept only as history. The design file
`Design.lean` is at revision 2 (no sorts, barrier restored); revision 1 is
kept as `Design.v1.lean`.

## Appendix A. Checklist of degenerate parameters

Ways a statement can be technically true and mean nothing, none of which
are bugs in the definitions. Worth a comment near `Realization`. Written
against the old API; `Hiding`, `Assumptions` and `Kσ` no longer exist, the
corresponding pitfalls survive as `Pre := False`, an empty input family,
and secrets fixed outside the quantified requests.

- `I := Empty`, or `Assumptions := fun _ => False`: vacuous. An empty
  contract, as in Clean.
- A secret fixed outside the quantified family: `∀ x, Hiding M (fun _ : Unit => …x…)`
  is `∀ x, ∃ Sim`, not `∃ Sim, ∀ x`, and holds with `Sim _ := pure [x]`.
  Section variables are the usual way this happens.
- An output that encodes the input: deterministic `Hiding` becomes
  automatic. Fine for a public output, disastrous for a hidden one.
- `ε ≥ 1` in any statistical statement.
- `Kσ := Unit` erases operation identity from the concrete view (trace
  length remains); a large `Kτ` reopens Issue 2.
- `Model.mapLeak ψ` with non-injective `ψ` coarsens the view; there is no
  theorem about how `Hiding` transfers along it.

## Appendix B. Where the two reviewers disagreed, and how it was settled

- *Wording of Issue 1.* Claude: "vacuous for share outputs". Codex: not
  every share-returning circuit is hiding; the defect is automatic
  declassification of the result. Settled in Codex's favour.
- *Fix for Issue 2.* Claude proposed domain-polymorphic kinds into a fixed
  `K : Type`. Codex: a fixed `K` cannot carry `D.F` payloads across
  domains; use `K : Type → Type` indexed by the clear field, and treat
  polymorphism as a convention rather than enforcement. Settled in Codex's
  favour at the time (Option 2A); **superseded** by the final decision,
  which removes kinds altogether (the header is the operation).
- *Constraining `leak`/`view`.* Claude proposed making declared leakage
  domain-polymorphic too, so it could only mention clear data. Codex: the
  disclosure policy is trusted by design and may legitimately depend on
  secrets; only the *automatic* observations (kinds, projections) must
  not. Claude conceded.
- *Meaning of `pubOut := ()`.* Claude called it "reveals nothing, even
  given later openings". Codex: it is stronger, "trace independent of the
  result"; "nothing beyond the output once opened" is `pubOut := id`.
  Claude conceded.
- *Enforcement (Issue 3).* Codex recommends a checked first-order
  front-end as the eventual fix. Claude holds that this partially reverses
  decision 001. **Superseded**: the author rejected the front-end even as
  a deferred option; the Lean DSL stays (Issue 3 item 5).
- *Efficiency of simulators (DESIGN:527).* Codex ranks the missing
  efficiency certificate as a top-six change. Claude treats it as a prose
  fix at this stage. Recorded as a prose fix in Issue 9, certificate in
  Package 3.
- *Assumptions.* Claude leaned to totalising where natural; Codex to the
  validity judgment as the default with totalised variants separately
  named. Settled: 4C default, 4E named alternative.
- Codex contributed Issues 3 (shape and enforcement), 4a (self-derived
  program), 5 (the false `randomCombination` claim and the joint-step gap),
  the `RealizesStat` output-error example, the wrong transitivity example,
  and Appendix A. Claude contributed Issues 1, 2, 4b, 7, 8, 10 and the
  prose table; both found 1, 2, 4b, 7, 8 independently.

**Rounds 3 and 4 (the redesign).** Codex (round 3) reviewed the
operation/operands proposal: agreed on multi-field via typed operands and
on composition surviving; corrected that a fixed `K : Type` cannot carry
clear payloads across domains, that a model could omit a clear response
(hence the structural clear-output channel), that universes need concrete
fields per interface, and that `Silent.Arith.hiding` becomes false; ranked
"adopt with changes". GPT (round 4, `gpt-6-astra`) reviewed the decided
design: confirmed the three-channel event, functionalities all the way,
`Valid` and the composition shapes; corrected the statistical bound to the
joint (the `b ← rand; reveal (x+b); pure b` example), the missing `∀ D` on
`Realization.impl` and the fully-applied check, the missing barrier in the
generic timed model, and interface-level `Has` proving nothing about
meaning (which led to the list hybrid); recommended 5A. Author's
overrides, all recorded: `leak` may depend on secrets (against Claude's
first Issue 1 item 3); a share is a share (against both reviewers' sort
index); the Lean DSL stays (against Codex's first-order front-end); the
one-equality `Has` (against Claude's five-field `Incl`); "programs", not
"circuits".

## Appendix C. Method

Both reviewers read DESIGN.md, the thirteen decision records and all Lean
files. Codex ran in a read-only sandbox (`codex exec -s read-only`,
`gpt-6-astra`), once independently, once with Claude's findings and eight
targeted questions, once on the operation/operands proposal, and once on the
decided design at reasoning effort xhigh. The decisions were then taken
issue by issue with the author. No file in the repository was modified
except this report. The redesigned core was typechecked in core Lean 4.29
without Mathlib (scratchpad `Design.lean` revision 2, `Hyb.lean`,
`HasF.lean`, `peek.lean`); the `PMF` layer and the old repository were
not compiled.
