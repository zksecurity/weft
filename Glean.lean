import Mathlib.Logic.Equiv.Defs
import Mathlib.Tactic.Ring
import Mathlib.Order.WithBot
import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Distributions.Uniform

/-!
# Glean — design sketch (working name)

A framework for verifying MPC circuits in Lean 4.  This file is the core:
signatures, circuits, domains, the interpreter in an arbitrary monad, the
laws it satisfies, the ideal models of the standard features, and the
example circuits from DESIGN.md with their theorems.
-/
namespace Glean

/-! ## 1. Signatures: what the ideal functionality offers -/

universe u

/-- A signature: `σ α` is the type of requests whose response has type `α`.
Universe-polymorphic so that a request may mention a field *type*
(`MultiField.lean`); everything else lives at `u = 0`. -/
abbrev Sig : Type (u + 1) := Type → Type u

/-- Sum of two signatures: an MPC that offers both feature sets. -/
inductive Sig.Sum (σ τ : Sig.{u}) (α : Type) : Type u where
  | inl : σ α → Sig.Sum σ τ α
  | inr : τ α → Sig.Sum σ τ α

@[inherit_doc] infixr:35 " ⊞ " => Sig.Sum

/-- `Has τ σ`: feature set `τ` is available inside `σ`. -/
class Has (τ σ : Sig.{u}) where
  inj : {α : Type} → τ α → σ α

instance Has.refl {σ : Sig} : Has σ σ := ⟨id⟩
instance Has.left {τ σ ρ : Sig} [Has τ σ] : Has τ (σ ⊞ ρ) := ⟨fun o => .inl (Has.inj o)⟩
instance Has.right {τ σ ρ : Sig} [Has τ ρ] : Has τ (σ ⊞ ρ) := ⟨fun o => .inr (Has.inj o)⟩

/-! ## 2. Circuits: programs talking to the functionality -/

/-- Free monad over `σ`: `pure`, or one request and a continuation.  There is
no parallel node: delay is computed from data dependencies (§4b), so
sequential `do`-code already gets the parallel count. -/
inductive Circ (σ : Sig.{u}) : Type → Type (max 1 u) where
  | pure {α : Type} : α → Circ σ α
  | call {α β : Type} : σ β → (β → Circ σ α) → Circ σ α

namespace Circ
variable {σ τ : Sig} {α β γ : Type}

def bind : Circ σ α → (α → Circ σ β) → Circ σ β
  | .pure a, f => f a
  | .call o k, f => .call o fun r => bind (k r) f

instance : Monad (Circ σ) where
  pure := Circ.pure
  bind := Circ.bind

@[simp] theorem bind_eq (c : Circ σ α) (f : α → Circ σ β) : c >>= f = Circ.bind c f := rfl
@[simp] theorem pure_eq (a : α) : (pure a : Circ σ α) = Circ.pure a := rfl
@[simp] theorem bind_pure' (a : α) (f : α → Circ σ β) : Circ.bind (.pure a) f = f a := rfl
@[simp] theorem bind_call {γ : Type} (o : σ γ) (k : γ → Circ σ α) (f : α → Circ σ β) :
    Circ.bind (.call o k) f = .call o fun r => Circ.bind (k r) f := rfl

/-- Invoke one operation of a feature set `τ` available in `σ`. -/
def op [Has τ σ] (o : τ α) : Circ σ α := .call (Has.inj o) .pure

/-- Realise every operation of `τ` by a circuit over `σ` (a handler), e.g.
multiplication via Beaver triples on top of `Lin ⊞ Reveal ⊞ MulTriple`. -/
def handle {α : Type} (h : {β : Type} → τ β → Circ σ β) : Circ τ α → Circ σ α
  | .pure a => .pure a
  | .call o k => bind (h o) fun r => handle h (k r)

/-- A circuit over a smaller feature set runs on any larger one. -/
def weaken {α : Type} [Has σ τ] : Circ σ α → Circ τ α := handle fun o => op o
end Circ

/-! ## 3. Domains and feature sets -/

/-- A domain fixes the clear type `F` and the (opaque) shared type `S`.
Circuits are polymorphic in `D`, so they cannot look inside `D.S`. -/
structure Domain where
  F : Type
  S : Type

/-- The ideal domain: a share *is* its value.  Used for semantics only. -/
abbrev Domain.ideal (F : Type) : Domain := ⟨F, F⟩

/-- Linear operations: free in every model. -/
inductive Lin (D : Domain) : Sig where
  | const : D.F → Lin D D.S
  | add   : D.S → D.S → Lin D D.S
  | sub   : D.S → D.S → Lin D D.S
  | smul  : D.F → D.S → Lin D D.S

/-- Secure multiplication. -/
inductive Mult (D : Domain) : Sig where
  | mult : D.S → D.S → Mult D D.S

/-- Opening a share to everyone (the interactive / reactive part). -/
inductive Reveal (D : Domain) : Sig where
  | reveal : D.S → Reveal D D.F

/-- A comparison sub-functionality some MPCs offer natively. -/
inductive Cmp (D : Domain) : Sig where
  | lt : D.S → D.S → Cmp D D.S

/-- A control dependency: the circuit is about to branch on revealed
values.  Semantically a no-op; in the timed domain it raises the control
clock to the reveal clock, so everything issued afterwards is scheduled
after those values are known.  Straight-line code never needs it. -/
inductive Barrier (D : Domain) : Sig where
  | barrier : Barrier D Unit

/-- A fresh, uniformly random shared value (unknown to everyone). -/
inductive Rand (D : Domain) : Sig where
  | rand : Rand D D.S

/-! Preprocessing boxes.  Each correlation is its own interface, named after
the functionality it is the interface of (decision 013): the response type
says the shape, the name says the promise, and the ideal model (§6) keeps
it.  Two correlations with the same shape are distinct interfaces. -/

/-- A multiplication (Beaver) triple `(a, b, a·b)`. -/
inductive MulTriple (D : Domain) : Sig where
  | get : MulTriple D (D.S × D.S × D.S)

/-- A square pair `(r, r²)`. -/
inductive SquarePair (D : Domain) : Sig where
  | get : SquarePair D (D.S × D.S)

/-- A double sharing `([r]_t, [r]_2t)`. -/
inductive DoubleSharing (D : Domain) : Sig where
  | get : DoubleSharing D (D.S × D.S)

/-- A public random value: everyone, including the adversary, learns it. -/
inductive PubCoin (D : Domain) : Sig where
  | coin : PubCoin D D.F

section Ops
variable {D : Domain} {σ : Sig}
def const [Has (Lin D) σ] (x : D.F) : Circ σ D.S := Circ.op (Lin.const x)
def add   [Has (Lin D) σ] (a b : D.S) : Circ σ D.S := Circ.op (Lin.add a b)
def sub   [Has (Lin D) σ] (a b : D.S) : Circ σ D.S := Circ.op (Lin.sub a b)
def smul  [Has (Lin D) σ] (x : D.F) (a : D.S) : Circ σ D.S := Circ.op (Lin.smul x a)
def mul   [Has (Mult D) σ] (a b : D.S) : Circ σ D.S := Circ.op (Mult.mult a b)
def reveal [Has (Reveal D) σ] (a : D.S) : Circ σ D.F := Circ.op (Reveal.reveal a)
def lt    [Has (Cmp D) σ] (a b : D.S) : Circ σ D.S := Circ.op (Cmp.lt a b)
def barrier (D : Domain) [Has (Barrier D) σ] : Circ σ Unit := Circ.op (Barrier.barrier (D := D))
def rand  [Has (Rand D) σ] : Circ σ D.S := Circ.op Rand.rand
def mulTriple     [Has (MulTriple D) σ]     : Circ σ (D.S × D.S × D.S) := Circ.op MulTriple.get
def squarePair    [Has (SquarePair D) σ]    : Circ σ (D.S × D.S) := Circ.op SquarePair.get
def doubleSharing [Has (DoubleSharing D) σ] : Circ σ (D.S × D.S) := Circ.op DoubleSharing.get
def coin   [Has (PubCoin D) σ] : Circ σ D.F := Circ.op PubCoin.coin
end Ops

/-- The standard arithmetic black box. -/
abbrev Std (D : Domain) : Sig := Lin D ⊞ Mult D ⊞ Reveal D
/-- A preprocessing-model functionality: no native multiplication. -/
abbrev Pre (D : Domain) : Sig := Lin D ⊞ Reveal D ⊞ MulTriple D

/-! ## 4. Semantics: values, leakage, cost

The interpreter is written once, for an arbitrary monad `m`; a model of a
functionality says, in `m`, what each operation returns and what it leaks.
Three instantiations matter:

* `m := PMF` (Mathlib's probability mass functions) is **the semantics**:
  `rand` is `PMF.uniformOfFintype`, and a run is a distribution over
  (output, revealed values).  Privacy is stated there.
* `m := Id` is **evaluation** of coin-free circuits: output, leakage and
  cost by `rfl`/`decide`.  Deterministic features are modelled at `Id`
  once and lifted (`Model.lift`) into any monad.
* `m := Sched` (a clock state, §4b) is **scheduling**: delay, computed
  from data dependencies.

There is no tape of coins: each draw is a fresh `bind` of a uniform
distribution, so `k` draws are *jointly* uniform on `F^k`, which is what
every mask argument needs (`Privacy.lean`).  A model has no state of its
own, so running `c >>= k` is running `c` and then `k` (`run_bind`); that
one law is what every composition theorem rests on. -/

/-- Ideal (black-box) semantics of a signature: what each operation returns
(in `m`, so possibly randomised) and what the adversary observes. -/
structure Model (σ : Sig) (L : Type) (m : Type → Type) where
  program : {α : Type} → σ α → m α
  /-- What the adversary observes, as a function of the request *and* the response. -/
  leak : {α : Type} → σ α → α → List L

namespace Model
variable {σ τ : Sig} {L L' : Type} {m : Type → Type}

def sum (M : Model σ L m) (N : Model τ L m) : Model (σ ⊞ τ) L m where
  program o := match o with | .inl o => M.program o | .inr o => N.program o
  leak o x := match o with | .inl o => M.leak o x | .inr o => N.leak o x

/-- Re-encode what a model leaks (e.g. to share one leakage type across fields). -/
def mapLeak (ψ : L → L') (M : Model σ L m) : Model σ L' m where
  program := M.program
  leak o x := (M.leak o x).map ψ

/-- A deterministic model, seen in any monad. -/
def lift (m : Type → Type) [Monad m] (M : Model σ L Id) : Model σ L m where
  program o := pure (M.program o).run
  leak := M.leak

theorem ext {M N : Model σ L m}
    (hp : ∀ {α} (o : σ α), M.program o = N.program o)
    (hl : ∀ {α} (o : σ α) (x : α), M.leak o x = N.leak o x) : M = N := by
  cases M; cases N
  simp only [Model.mk.injEq]
  exact ⟨funext fun _ => funext fun o => hp o, funext fun _ => funext fun o => funext fun x => hl o x⟩

@[simp] theorem lift_program [Monad m] (M : Model σ L Id) {α} (o : σ α) :
    (M.lift m).program o = pure (M.program o).run := rfl
@[simp] theorem lift_leak [Monad m] (M : Model σ L Id) {α} (o : σ α) (x : α) :
    (M.lift m).leak o x = M.leak o x := rfl

theorem lift_sum [Monad m] (M : Model σ L Id) (N : Model τ L Id) :
    (M.sum N).lift m = (M.lift m).sum (N.lift m) :=
  ext (fun o => by cases o <;> rfl) (fun o _ => by cases o <;> rfl)
end Model

/-- The price of an operation on an MPC: its latency (rounds) and its
communication.  Latency feeds the timed domain, communication the additive
cost model. -/
structure Price where
  delay : Nat
  comm  : Nat
  deriving DecidableEq, Repr

/-- A cost model: a price for each operation, in an additive monoid of
costs (`ℕ`, `WithTop ℕ` with `⊤` for "unsupported", `Unit` for none).
Delay is not a cost in this sense; it is computed from data dependencies
in the timed domain (§4b). -/
structure CostModel (σ : Sig) (C : Type) where
  op : {α : Type} → σ α → C

def CostModel.unit {σ : Sig} : CostModel σ Unit := ⟨fun _ => ()⟩

/-- What one run accumulates besides its result. -/
structure Trace (C L : Type) where
  cost : C
  leak : List L

namespace Trace
variable {C L : Type} [AddMonoid C]
def seq (t u : Trace C L) : Trace C L := ⟨t.cost + u.cost, t.leak ++ u.leak⟩
def zero : Trace C L := ⟨0, []⟩
@[simp] theorem zero_leak : (zero : Trace C L).leak = [] := rfl
@[simp] theorem zero_cost : (zero : Trace C L).cost = 0 := rfl
@[simp] theorem seq_leak (t u : Trace C L) : (seq t u).leak = t.leak ++ u.leak := rfl
@[simp] theorem seq_cost (t u : Trace C L) : (seq t u).cost = t.cost + u.cost := rfl
@[simp] theorem zero_seq (t : Trace C L) : seq zero t = t := by simp [seq, zero]
@[simp] theorem seq_zero (t : Trace C L) : seq t zero = t := by simp [seq, zero]
@[simp] theorem seq_assoc (t u v : Trace C L) : seq (seq t u) v = seq t (seq u v) := by
  simp [seq, add_assoc]
end Trace

/-- Run a circuit against a model: result, leakage, cost. -/
def run {σ : Sig} {L C α : Type} [AddMonoid C] {m : Type → Type} [Monad m]
    (M : Model σ L m) (K : CostModel σ C) : Circ σ α → m (α × Trace C L)
  | .pure a => pure (a, Trace.zero)
  | .call o k => do
    let x ← M.program o
    let r ← run M K (k x)
    pure (r.1, Trace.seq ⟨K.op o, M.leak o x⟩ r.2)

section Observables
variable {σ : Sig} {L C α : Type} [AddMonoid C]

/-- Evaluation (`m := Id`): output, leakage and cost of one run. -/
def output (M : Model σ L Id) (c : Circ σ α) : α := (Id.run (run M CostModel.unit c)).1
def leak (M : Model σ L Id) (c : Circ σ α) : List L := (Id.run (run M CostModel.unit c)).2.leak
def cost (M : Model σ L Id) (K : CostModel σ C) (c : Circ σ α) : C := (Id.run (run M K c)).2.cost

/-- **The semantics** (`m := PMF`): the distribution of (output, revealed values). -/
noncomputable def dist (M : Model σ L PMF) (c : Circ σ α) : PMF (α × List L) :=
  (fun p => (p.1, p.2.leak)) <$> run M CostModel.unit c
end Observables

/-! ### The laws

`run_bind`: running a sequential composition is running the parts.  It holds
in every lawful monad because a model carries no state, and it is the only
fact about the interpreter that composition theorems need.  `run_lift`: a
coin-free circuit under a lifted model is a point; so its semantics is its
evaluation, and `rfl` proofs at `Id` transfer to `PMF`. -/

section Laws
variable {σ : Sig} {L C α β : Type} [AddMonoid C] {m : Type → Type} [Monad m]

@[simp] theorem run_pure (M : Model σ L m) (K : CostModel σ C) (a : α) :
    run M K (.pure a) = pure (a, Trace.zero) := rfl

theorem run_call (M : Model σ L m) (K : CostModel σ C) {γ : Type} (o : σ γ) (k : γ → Circ σ α) :
    run M K (.call o k) = (do
      let x ← M.program o
      let r ← run M K (k x)
      pure (r.1, Trace.seq ⟨K.op o, M.leak o x⟩ r.2)) := rfl

/-- `>>=`, `pure` and `<$>` on `PMF` are Mathlib's `PMF.bind`, `PMF.pure`, `PMF.map`. -/
theorem PMF.monad_bind_eq_bind {α β : Type} (p : PMF α) (f : α → PMF β) : p >>= f = p.bind f := rfl
theorem PMF.monad_pure_eq_pure {α : Type} (a : α) : (pure a : PMF α) = PMF.pure a := rfl

variable [LawfulMonad m]

theorem run_bind (M : Model σ L m) (K : CostModel σ C) (c : Circ σ α) (k : α → Circ σ β) :
    run M K (Circ.bind c k) = (do
      let r ← run M K c
      let s ← run M K (k r.1)
      pure (s.1, Trace.seq r.2 s.2)) := by
  induction c with
  | pure a => simp [run]
  | call o k' ih => simp only [Circ.bind_call, run_call, ih, bind_assoc, pure_bind, Trace.seq_assoc]

theorem run_lift (M : Model σ L Id) (K : CostModel σ C) (c : Circ σ α) :
    run (M.lift m) K c = pure (Id.run (run M K c)) := by
  induction c with
  | pure a => rfl
  | call o k ih =>
    simp only [run_call, ih, Model.lift_program, Model.lift_leak]
    exact (pure_bind _ _).trans (by simp only [pure_bind]; rfl)

theorem dist_lift (M : Model σ L Id) (c : Circ σ α) :
    dist (M.lift PMF) c = pure (output M c, leak M c) := by
  simp [dist, run_lift, output, leak]

theorem dist_call (M : Model σ L PMF) {γ : Type} (o : σ γ) (k : γ → Circ σ α) :
    dist M (.call o k) = (do
      let x ← M.program o
      let r ← dist M (k x)
      pure (r.1, M.leak o x ++ r.2)) := by
  simp [dist, run_call, Trace.seq]

theorem dist_bind (M : Model σ L PMF) (c : Circ σ α) (k : α → Circ σ β) :
    dist M (Circ.bind c k) = (do
      let r ← dist M c
      let s ← dist M (k r.1)
      pure (s.1, r.2 ++ s.2)) := by
  simp [dist, run_bind, Trace.seq]
end Laws

/-! ## 4b. Delay: the timed domain

Delay is not accumulated by the interpreter; it is *computed from data
dependencies*.  Run the same circuit in the **timed domain**, where every
share carries the round at which it becomes available (clear values stay
plain, so generic circuits branch on them as usual).  An operation's
result is available at `max(inputs' times, clock) + latency`.  Two clocks
in the scheduling monad cover what the dependency graph cannot see:
the *reveal clock* (latest reveal so far), which any operation with a clear
argument inherits since clear computation is opaque, and the *control
clock*, raised to the reveal clock by `barrier` where a circuit branches
on a revealed value.  The delay of a circuit is the time of its output.
Timed models are evaluation models: coins get a dummy value, which delay
never depends on. -/

/-- Scheduling state. -/
structure Clock where
  /-- Control clock: nothing issued after a `barrier` starts before it. -/
  clock    : Nat := 0
  /-- Reveal clock: the latest time at which a value was revealed. -/
  revealed : Nat := 0

/-- The scheduling monad: evaluation with a clock. -/
abbrev Sched : Type → Type := StateT Clock Id

/-- A value together with the round at which it is available. -/
structure Timed (F : Type) where
  val  : F
  time : Nat

/-- The timed domain: shares carry a ready time, clear values are plain. -/
abbrev Domain.timed (F : Type) : Domain := ⟨F, Timed F⟩

/-- Result available `ℓ` after its inputs and the clock. -/
def Timed.after {F : Type} (ts : List Nat) (ℓ : Nat) (v : F) : Sched (Timed F) :=
  fun s => (⟨v, ts.foldr max s.clock + ℓ⟩, s)

section TimedModels
variable (F : Type) [Add F] [Mul F] [Sub F] [Inhabited F]
local notation "𝕋" => Domain.timed F

/-- Linear operations: free, ready when their inputs (and the clock) are. -/
def Lin.timed : Model (Lin 𝕋) F Sched where
  program o := match o with
    | .const x  => fun s => (⟨x, max s.clock s.revealed⟩, s)               -- clear argument: may depend on anything revealed
    | .add a b  => Timed.after [a.time, b.time] 0 (a.val + b.val)
    | .sub a b  => Timed.after [a.time, b.time] 0 (a.val - b.val)
    | .smul x a => fun s => (⟨x * a.val, max (max a.time s.clock) s.revealed⟩, s)   -- likewise
  leak _ _ := []

def Mult.timed (ℓ : Nat) : Model (Mult 𝕋) F Sched where
  program o := match o with | .mult a b => Timed.after [a.time, b.time] ℓ (a.val * b.val)
  leak _ _ := []

/-- Reveal: the value is clear `ℓ` later, and the reveal clock records when.
Independent reveals stay in the same round; only a `barrier` serialises
what follows. -/
def Reveal.timed (ℓ : Nat) : Model (Reveal 𝕋) F Sched where
  program o := match o with
    | .reveal a => fun s =>
      let t := max a.time s.clock + ℓ
      (a.val, { s with revealed := max s.revealed t })
  leak o x := match o with | .reveal _ => [x]

/-- A barrier: the circuit branches on revealed values, so everything after
it waits for them. -/
def Barrier.timed : Model (Barrier 𝕋) F Sched where
  program o := match o with
    | .barrier => fun s => ((), { s with clock := max s.clock s.revealed })
  leak _ _ := []

/-- Semantically, a barrier does nothing. -/
def Barrier.ideal {L : Type} (F : Type) : Model (Barrier (Domain.ideal F)) L Id where
  program o := match o with | .barrier => pure ()
  leak _ _ := []

/-- A random share is available at once (at the clock); its value is a dummy. -/
def Rand.timed : Model (Rand 𝕋) F Sched where
  program o := match o with | .rand => fun s => (⟨default, s.clock⟩, s)
  leak _ _ := []

/-- A triple from preprocessing: available at the clock, plus `ℓ` if generated online. -/
def MulTriple.timed (ℓ : Nat) : Model (MulTriple 𝕋) F Sched where
  program o := match o with
    | .get => fun s =>
      let t := s.clock + ℓ
      ((⟨default, t⟩, ⟨default, t⟩, ⟨default * default, t⟩), s)
  leak _ _ := []

/-- The arithmetic black box, timed: multiplication and reveal one round each. -/
def Std.timed (ℓmult ℓreveal : Nat := 1) : Model (Std 𝕋) F Sched :=
  (Lin.timed F).sum ((Mult.timed F ℓmult).sum (Reveal.timed F ℓreveal))

/-- The preprocessing functionality, timed: `ℓtriple = 0` when precomputed. -/
def Pre.timed (ℓreveal ℓtriple : Nat) : Model (Pre 𝕋) F Sched :=
  (Lin.timed F).sum ((Reveal.timed F ℓreveal).sum (MulTriple.timed F ℓtriple))

variable {F}

/-- A scheduled run: output and final clocks (inputs available at round 0). -/
def Sched.run {σ : Sig} {L α : Type} (M : Model σ L Sched) (c : Circ σ α) : α × Clock :=
  let p := Id.run (StateT.run (Glean.run M CostModel.unit c) {})
  (p.1.1, p.2)
def Sched.output {σ : Sig} {L α : Type} (M : Model σ L Sched) (c : Circ σ α) : α := (Sched.run M c).1

/-- The delay of a circuit with a shared output: when it is available. -/
def delayOn {σ : Sig} {L : Type} (M : Model σ L Sched) (c : Circ σ (Timed F)) : Nat :=
  (Sched.output M c).time
/-- The delay of a circuit with a clear output: the time of its last reveal. -/
def delayClear {σ : Sig} {L α : Type} (M : Model σ L Sched) (c : Circ σ α) : Nat :=
  (Sched.run M c).2.revealed
end TimedModels

/-- `delay F M c`: delay of a circuit over the standard functionality. -/
abbrev delay (F : Type) {L : Type} (M : Model (Std (Domain.timed F)) L Sched)
    (c : Circ (Std (Domain.timed F)) (Timed F)) : Nat := delayOn M c

/-! ## 5. Properties

Privacy is stated on the semantics, i.e. on `PMF`: the distribution of the
real run equals (or is close to) the distribution of an ideal run in which
a simulator invents the revealed values from what the functionality
declares.  No tapes, no bijections in the definition; the proof rule for
masks is a lemma about uniform distributions (`Privacy.lean`). -/

section Props
variable {σ : Sig} {L I α : Type}

/-- Total variation distance between two discrete distributions. -/
noncomputable def PMF.statDist {β : Type} (p q : PMF β) : ENNReal := ∑' b, (p b - q b)

/-- **Hiding (top level).**  The revealed values are simulatable from the
output alone: the real distribution of (output, reveals) equals the ideal
one where the output is drawn as the circuit draws it and the reveals are
produced by a simulator that sees only the output, with fresh coins. -/
def Hiding (M : Model σ L PMF) (c : I → Circ σ α) : Prop :=
  ∃ Sim : α → PMF (List L), ∀ i,
    dist M (c i) = do
      let y ← Prod.fst <$> dist M (c i)
      let s ← Sim y
      pure (y, s)

/-- Statistical version: within `ε` in total variation. -/
def HidingStat (M : Model σ L PMF) (ε : ENNReal) (c : I → Circ σ α) : Prop :=
  ∃ Sim : α → PMF (List L), ∀ i,
    PMF.statDist (dist M (c i))
      (do let y ← Prod.fst <$> dist M (c i); let s ← Sim y; pure (y, s)) ≤ ε

/-- A run that is a point distribution whose leakage is a function of the output is hiding. -/
theorem hiding_of_pure (M : Model σ L PMF) (c : I → Circ σ α) (f : I → α) (sim : α → List L)
    (h : ∀ i, dist M (c i) = pure (f i, sim (f i))) : Hiding M c := by
  refine ⟨fun y => pure (sim y), fun i => ?_⟩
  rw [h i]
  simp

/-- **The mask lemma.**  The image of the uniform distribution under a
bijection is uniform: a revealed value `f(secret, mask)` that is, for each
secret, a bijective function of a fresh uniform mask is itself uniform and
independent of the secret.  Applied to *jointly* uniform masks (`Fin k → F`)
it covers every revealed vector at once (`Privacy.lean`). -/
theorem uniform_map_equiv {α β : Type} [Fintype α] [Nonempty α] [Fintype β] [Nonempty β] (e : α ≃ β) :
    (PMF.uniformOfFintype α).map e = PMF.uniformOfFintype β := by
  ext b
  rw [PMF.map_apply, PMF.uniformOfFintype_apply, tsum_eq_single (e.symm b)]
  · simp [Fintype.card_congr e]
  · intro a ha
    have : b ≠ e a := fun h => ha (by rw [h, Equiv.symm_apply_apply])
    simp [this]

/-- Coin-free circuits: hiding is "the leakage is a function of the output",
checked by evaluation. -/
theorem Hiding.of_lift (M : Model σ L Id) (c : I → Circ σ α) (sim : α → List L)
    (h : ∀ i, leak M (c i) = sim (output M (c i))) : Hiding (M.lift PMF) c :=
  hiding_of_pure _ _ (fun i => output M (c i)) sim fun i => by rw [dist_lift, h i]
end Props

/-! ## 6. Ideal models for the standard features

Deterministic features are modelled at `Id`; `Model.lift PMF` is their
semantics.  Randomised features are modelled at `PMF` directly. -/

section Ideal
variable (F : Type) [Add F] [Mul F] [Sub F]

def Lin.ideal {L} : Model (Lin (.ideal F)) L Id where
  program o := match o with
    | .const x => pure x | .add a b => pure (a + b) | .sub a b => pure (a - b) | .smul x a => pure (x * a)
  leak _ _ := []

def Mult.ideal {L} : Model (Mult (.ideal F)) L Id where
  program o := match o with | .mult a b => pure (a * b)
  leak _ _ := []

/-- Revealing returns the value and leaks it. -/
def Reveal.ideal : Model (Reveal (.ideal F)) F Id where
  program o := match o with | .reveal x => pure x
  leak o x := match o with | .reveal _ => [x]

/-- The arithmetic black box. -/
def Std.ideal : Model (Std (.ideal F)) F Id :=
  (Lin.ideal F).sum ((Mult.ideal F).sum (Reveal.ideal F))
end Ideal

section IdealRandom
variable (F : Type) [Add F] [Mul F] [Sub F] [Fintype F] [Nonempty F]

/-- Uniform coins over a finite alphabet: Mathlib's `PMF.uniformOfFintype`, by another name. -/
notation "uniform" => PMF.uniformOfFintype

/-- A fresh random share is one uniform draw; nothing is leaked. -/
noncomputable def Rand.ideal {L} : Model (Rand (.ideal F)) L PMF where
  program o := match o with | .rand => uniform F
  leak _ _ := []

/-- A public coin is one uniform draw, and it is leaked. -/
noncomputable def PubCoin.ideal : Model (PubCoin (.ideal F)) F PMF where
  program o := match o with | .coin => uniform F
  leak o x := match o with | .coin => [x]

/-- A correlation is a deterministic function of `k` *jointly uniform* coins. -/
structure Correlation (R T : Type) where
  k     : Nat
  build : (Fin k → R) → T

/-- Sampling a correlation: the `k` coins are drawn jointly uniform on `R^k`. -/
noncomputable def Correlation.sample {T : Type} (c : Correlation F T) : PMF T :=
  (uniform (Fin c.k → F)).map c.build

def MulTriple.corr     : Correlation F (F × F × F) := ⟨2, fun x => (x 0, x 1, x 0 * x 1)⟩
def SquarePair.corr    : Correlation F (F × F)     := ⟨1, fun x => (x 0, x 0 * x 0)⟩
/-- In the black box a double sharing is one value seen twice: sharing degree
is not observable.  If a circuit must track it, put it in the domain. -/
def DoubleSharing.corr : Correlation F (F × F)     := ⟨1, fun x => (x 0, x 0)⟩

/-- The ideal model of a preprocessing box: sample its correlation, leak nothing.
This is the promise the interface's name makes. -/
noncomputable def MulTriple.ideal {L} : Model (MulTriple (.ideal F)) L PMF where
  program o := match o with | .get => (MulTriple.corr F).sample
  leak _ _ := []
noncomputable def SquarePair.ideal {L} : Model (SquarePair (.ideal F)) L PMF where
  program o := match o with | .get => (SquarePair.corr F).sample
  leak _ _ := []
noncomputable def DoubleSharing.ideal {L} : Model (DoubleSharing (.ideal F)) L PMF where
  program o := match o with | .get => (DoubleSharing.corr F).sample
  leak _ _ := []

/-- The preprocessing functionality, as a distribution. -/
noncomputable def Pre.ideal : Model (Pre (.ideal F)) F PMF :=
  ((Lin.ideal F).lift PMF).sum (((Reveal.ideal F).lift PMF).sum (MulTriple.ideal F))

/-! ### Evaluation models: coins fixed to a dummy value

For cost and delay of circuits that draw coins, an `Id` model with a dummy
coin is enough, because neither depends on the coin's value (only on the
circuit's shape).  Values computed under these models are meaningless. -/
def Rand.eval {L} [Inhabited F] : Model (Rand (.ideal F)) L Id where
  program o := match o with | .rand => pure default
  leak _ _ := []
def MulTriple.eval {L} [Inhabited F] : Model (MulTriple (.ideal F)) L Id where
  program o := match o with | .get => pure (default, default, default * default)
  leak _ _ := []
def Pre.eval [Inhabited F] : Model (Pre (.ideal F)) F Id :=
  (Lin.ideal F).sum ((Reveal.ideal F).sum (MulTriple.eval F))
end IdealRandom

/-- A fresh random share that is *nonzero* (uniform on `F \ {0}`).  Gadgets
that mask by multiplication (inversion) use it, so that correctness is
perfect: the functionality, not luck, guarantees the mask is invertible. -/
inductive RandNZ (D : Domain) : Sig where
  | randNZ : RandNZ D D.S

def randNZ {D : Domain} {σ : Sig} [Has (RandNZ D) σ] : Circ σ D.S := Circ.op RandNZ.randNZ

instance {F : Type} [Zero F] [Nontrivial F] : Nonempty {x : F // x ≠ 0} :=
  let ⟨x, hx⟩ := exists_ne (0 : F); ⟨⟨x, hx⟩⟩

noncomputable def RandNZ.ideal (F : Type) [Zero F] [Nontrivial F] [Fintype F] [DecidableEq F] {L} :
    Model (RandNZ (.ideal F)) L PMF where
  program o := match o with | .randNZ => (uniform {x : F // x ≠ 0}).map Subtype.val
  leak _ _ := []

/-! ## 7. Example circuits (polymorphic in the domain and the signature) -/

namespace Examples
variable {D : Domain} {σ : Sig}

/-- Sum of shares: only linear ops, hence free and silent. -/
def sumAll [Has (Lin D) σ] [OfNat D.F 0] : List D.S → Circ σ D.S
  | [] => const (0 : D.F)
  | [x] => pure x
  | x :: xs => do let s ← sumAll xs; add x s

/-- Inner product: the multiplications are independent, so one round, then a
free sum.  Nothing says "parallel": the timed domain sees it. -/
def inner [Has (Lin D) σ] [Has (Mult D) σ] [OfNat D.F 0] (xs ys : List D.S) : Circ σ D.S := do
  let ps ← (xs.zip ys).mapM fun p => mul p.1 p.2
  sumAll ps

/-- Two dependent multiplications: two rounds. -/
def mul3 [Has (Mult D) σ] (a b c : D.S) : Circ σ D.S := do
  let ab ← mul a b
  mul ab c

/-- Balanced product tree: `depth` delay. -/
inductive Tree (α : Type) where
  | leaf : α → Tree α
  | node : Tree α → Tree α → Tree α

def prodTree [Has (Mult D) σ] : Tree D.S → Circ σ D.S
  | .leaf x => pure x
  | .node l r => do
    let a ← prodTree l
    let b ← prodTree r
    mul a b

/-- Reveal the product: leaks exactly the output, hence hiding. -/
def openMul [Has (Mult D) σ] [Has (Reveal D) σ] (a b : D.S) : Circ σ D.F := do
  let p ← mul a b
  reveal p

/-- Reveal both inputs and multiply in the clear: correct, but not hiding. -/
def leakyMul [Has (Reveal D) σ] [Mul D.F] (a b : D.S) : Circ σ D.F := do
  let x ← reveal a
  let y ← reveal b
  pure (x * y)

/-- The reactive pattern: open, compute in the clear, insert back. -/
def divByOpened [Has (Lin D) σ] [Has (Reveal D) σ] [Div D.F] [OfNat D.F 1]
    (x d : D.S) : Circ σ D.S := do
  let dv ← reveal d          -- d is public information in this application
  smul (1 / dv) x            -- 1/d computed in the clear, multiplied back in

/-- `max a b = a + [a < b] · (b - a)`: a comparison round plus one mult round. -/
def maxOf [Has (Lin D) σ] [Has (Mult D) σ] [Has (Cmp D) σ] (a b : D.S) : Circ σ D.S := do
  let c ← lt a b
  let d ← sub b a
  let e ← mul c d
  add a e

/-! ### A circuit over the standard functionality, as a user writes it -/

/-- `⟨xs, ys⟩ + c`.  One round: the products in parallel, then free linear ops. -/
def dotPlus [Has (Lin D) σ] [Has (Mult D) σ] [OfNat D.F 0]
    (xs ys : List D.S) (c : D.F) : Circ σ D.S := do
  let ps ← (xs.zip ys).mapM fun p => mul p.1 p.2
  let s ← sumAll ps
  let k ← const c
  add s k

/-- Horner evaluation of `Σ aᵢ xⁱ`: one multiplication per coefficient,
each depending on the last, so `n` delay.  The honest cost of the schedule
you wrote; a parallel-prefix version would be `log n`. -/
def horner [Has (Lin D) σ] [Has (Mult D) σ] [OfNat D.F 0]
    (x : D.S) : List D.S → Circ σ D.S
  | [] => const (0 : D.F)
  | a :: as => do
    let r ← horner x as
    let t ← mul r x
    add t a

/-! ### Assembling correlations: the offline phase as a handler -/

/-- Triples from random shares and one secure multiplication. -/
def tripleFromRand [Has (Rand D) σ] [Has (Mult D) σ] : {β : Type} → MulTriple D β → Circ σ β
  | _, .get => do
    let a ← rand
    let b ← rand
    let c ← mul a b
    pure (a, b, c)

/-- Squares from random shares. -/
def squareFromRand [Has (Rand D) σ] [Has (Mult D) σ] : {β : Type} → SquarePair D β → Circ σ β
  | _, .get => do
    let r ← rand
    let r2 ← mul r r
    pure (r, r2)

/-- A public coin used as a challenge: a random linear combination of shares. -/
def randomCombination [Has (Lin D) σ] [Has (PubCoin D) σ] [Mul D.F] [OfNat D.F 0]
    (xs : List D.S) : Circ σ D.S := do
  let r ← coin
  let rec go (p : D.F) : List D.S → Circ σ D.S
    | [] => const (0 : D.F)
    | x :: xs => do
      let t ← smul p x
      let s ← go (p * r) xs
      add t s
  go r xs

/-- Beaver multiplication: a handler realising `Mult` on top of `Pre`.
Reveals `x - a` and `y - b` (independent, so one round), then only linear ops. -/
def beaver [Has (Lin D) σ] [Has (Reveal D) σ] [Has (MulTriple D) σ] [Mul D.F] :
    {β : Type} → Mult D β → Circ σ β
  | _, .mult x y => do
    let (a, b, c) ← mulTriple
    let u₁ ← sub x a
    let e ← reveal u₁
    let u₂ ← sub y b
    let d ← reveal u₂
    -- x·y = c + e·b + d·a + e·d
    let t₁ ← smul e b
    let t₂ ← smul d a
    let s ← add c t₁
    let s ← add s t₂
    let ed ← const (e * d)
    add s ed

/-- Any `Std` circuit runs on a preprocessing functionality. -/
def onPre [Mul D.F] {α : Type} : Circ (Std D) α → Circ (Pre D) α :=
  Circ.handle fun o => match o with
    | .inl o => Circ.op o
    | .inr (.inl o) => beaver o
    | .inr (.inr o) => Circ.op o

/-! ### The shape of the theorems -/

section Theorems
variable (F : Type) [Add F] [Mul F] [Sub F]
local notation "𝕀" => Domain.ideal F

-- Functional correctness (against the ideal model), by evaluation.
example (a b c : F) :
    output (Std.ideal F) (mul3 (D := 𝕀) (σ := Std 𝕀) a b c) = a * b * c := rfl

-- Delay, from data dependencies in the timed domain (inputs available at round 0).
local notation "𝕋" => Domain.timed F
local notation "⟪" x "⟫" => (⟨x, 0⟩ : Timed F)
example [Inhabited F] (a b c : F) :
    delay F (Std.timed F) (mul3 (D := 𝕋) (σ := Std 𝕋) ⟪a⟫ ⟪b⟫ ⟪c⟫) = 2 := rfl
-- The product tree is written with plain binds and still costs its depth: the two
-- subtrees do not depend on each other, and the pass sees it.
example [Inhabited F] (a b c d : F) :
    delay F (Std.timed F)
      (prodTree (D := 𝕋) (σ := Std 𝕋) (.node (.node (.leaf ⟪a⟫) (.leaf ⟪b⟫)) (.node (.leaf ⟪c⟫) (.leaf ⟪d⟫))))
      = 2 := rfl

-- Leakage is computed, not asserted.
example (a b : F) : leak (Std.ideal F) (openMul (D := 𝕀) (σ := Std 𝕀) a b) = [a * b] := rfl
example (a b : F) : leak (Std.ideal F) (leakyMul (D := 𝕀) (σ := Std 𝕀) a b) = [a, b] := rfl

-- Hiding (coin-free): the leakage is a function of the output, checked by evaluation.
theorem openMul_hiding :
    Hiding ((Std.ideal F).lift PMF) (fun p : F × F => openMul (D := 𝕀) (σ := Std 𝕀) p.1 p.2) :=
  Hiding.of_lift _ _ (fun v => [v]) fun _ => rfl

-- Not hiding: two inputs with the same output but different leakage.  The
-- simulator would have to output `[1, 2]` and `[2, 1]` with certainty.
theorem leakyMul_not_hiding :
    ¬ Hiding ((Std.ideal Int).lift PMF) (fun p : Int × Int => leakyMul (D := .ideal Int) (σ := Std _) p.1 p.2) := by
  rintro ⟨Sim, h⟩
  have h₁ := h (1, 2)
  have h₂ := h (2, 1)
  rw [dist_lift] at h₁ h₂
  have e₁ : output (Std.ideal Int) (leakyMul (D := .ideal Int) (σ := Std _) 1 2) = 2 := rfl
  have e₂ : output (Std.ideal Int) (leakyMul (D := .ideal Int) (σ := Std _) 2 1) = 2 := rfl
  have l₁ : leak (Std.ideal Int) (leakyMul (D := .ideal Int) (σ := Std _) 1 2) = [1, 2] := rfl
  have l₂ : leak (Std.ideal Int) (leakyMul (D := .ideal Int) (σ := Std _) 2 1) = [2, 1] := rfl
  rw [e₁, l₁] at h₁
  rw [e₂, l₂] at h₂
  simp only [map_pure, pure_bind] at h₁ h₂
  simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure] at h₁ h₂
  -- both runs are points, so `Sim 2` is a point at `[1,2]` and at `[2,1]`
  have s₁ := congrArg PMF.support h₁
  have s₂ := congrArg PMF.support h₂
  rw [PMF.support_pure, PMF.support_bind] at s₁ s₂
  obtain ⟨l, hl⟩ := (Sim 2).support_nonempty
  have m₁ : ((2 : Int), l) ∈ ⋃ s ∈ (Sim 2).support, (PMF.pure ((2 : Int), s)).support :=
    Set.mem_iUnion₂.2 ⟨l, hl, by simp⟩
  have m₂ := m₁
  rw [← s₁] at m₁
  rw [← s₂] at m₂
  simp at m₁ m₂
  simp [m₁] at m₂

-- Standard-functionality circuits: correctness, delay, silence.
section
variable [OfNat F 0] [Inhabited F]
example (a b c : F) (k : F) :
    output (Std.ideal F) (dotPlus (D := 𝕀) (σ := Std 𝕀) [a, b] [c, c] k) = a * c + b * c + k := rfl
example (a b : F) (k : F) :
    delay F (Std.timed F) (dotPlus (D := 𝕋) (σ := Std 𝕋) [⟪a⟫, ⟪b⟫] [⟪a⟫, ⟪b⟫] k) = 1 := rfl
example (x a₀ a₁ a₂ : F) :
    delay F (Std.timed F) (horner (D := 𝕋) (σ := Std 𝕋) ⟪x⟫ [⟪a₀⟫, ⟪a₁⟫, ⟪a₂⟫]) = 3 := rfl
example (x a₀ a₁ a₂ : F) :
    leak (Std.ideal F) (horner (D := 𝕀) (σ := Std 𝕀) x [a₀, a₁, a₂]) = [] := rfl
end

/-! #### Beaver multiplication: coins, handlers, and cost models at once -/

-- The same circuit has delay 1 with precomputed triples and 3 when triples are
-- generated online in two rounds: the two reveals are independent (one round).
example [Inhabited F] (x y : F) :
    delayOn (Pre.timed F 1 0) (onPre (D := 𝕋) (mul (D := 𝕋) ⟪x⟫ ⟪y⟫)) = 1 := rfl
example [Inhabited F] (x y : F) :
    delayOn (Pre.timed F 1 2) (onPre (D := 𝕋) (mul (D := 𝕋) ⟪x⟫ ⟪y⟫)) = 3 := rfl

-- The offline phase, timed: a triple costs one multiplication round when
-- assembled from random shares, and the assembly is silent.
abbrev OffSig (D : Domain) : Sig := Lin D ⊞ Mult D ⊞ Rand D
def Off.eval [Inhabited F] : Model (OffSig 𝕀) F Id := (Lin.ideal F).sum ((Mult.ideal F).sum (Rand.eval F))
def Off.timed [Inhabited F] : Model (OffSig 𝕋) F Sched := (Lin.timed F).sum ((Mult.timed F 1).sum (Rand.timed F))

example [Inhabited F] :
    (Sched.output (Off.timed F) (Circ.handle (tripleFromRand (D := 𝕋)) (mulTriple (D := 𝕋)))).2.2.time = 1 := rfl
example [Inhabited F] :
    leak (Off.eval F) (Circ.handle (tripleFromRand (D := 𝕀)) (mulTriple (D := 𝕀))) = [] := rfl

/-! #### Beaver multiplication is hiding: the semantics, in `PMF`

The run of `onPre (mul x y)` is: draw `(a, b)` jointly uniform on `F²`,
reveal `(x - a, y - b)`, output `x·y`.  The revealed pair is the image of a
uniform pair under a bijection, hence uniform and independent of `(x, y)`;
the simulator draws a fresh uniform pair.  Everything below is the
distribution semantics, unfolded by `simp`, plus one lemma about uniform
distributions (`Privacy.lean` states it in general; here it is inlined). -/

end Theorems

section BeaverPrivacy
variable (F : Type) [Field F] [Fintype F]
local notation "𝕀" => Domain.ideal F

omit [Fintype F] in
theorem beaver_correct (x y : F) (v : Fin 2 → F) :
    v 0 * v 1 + (x - v 0) * v 1 + (y - v 1) * v 0 + (x - v 0) * (y - v 1) = x * y := by ring

theorem beaver_hiding :
    Hiding (Pre.ideal F) (fun p : F × F => onPre (D := 𝕀) (mul (D := 𝕀) p.1 p.2)) := by
  -- the simulator: a fresh uniform pair, presented as the two opened values
  refine ⟨fun _ => (uniform (F × F)).map fun q => [q.1, q.2], fun p => ?_⟩
  -- the real distribution, unfolded
  have real : dist (Pre.ideal F) (onPre (D := 𝕀) (mul (D := 𝕀) p.1 p.2)) =
      (uniform (Fin 2 → F)).bind fun v => pure (p.1 * p.2, [p.1 - v 0, p.2 - v 1]) := by
    simp [dist, onPre, mul, Circ.op, Circ.handle, beaver, Pre.ideal, Model.sum, Lin.ideal,
      Reveal.ideal, MulTriple.ideal, Correlation.sample, MulTriple.corr, sub, reveal, smul, add,
      const, mulTriple, Has.inj, Has.left, Has.right, Has.refl, run, Trace.seq,
      PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
      PMF.monad_map_eq_map, PMF.map_bind, PMF.pure_map, PMF.bind_map, PMF.bind_bind, Function.comp_def]
    congr 1
    funext v
    rw [beaver_correct]
  rw [real]
  -- the output is a point, so the ideal side is `Sim (x·y)` tagged with the output
  have out : Prod.fst <$> ((uniform (Fin 2 → F)).bind fun v => pure (p.1 * p.2, [p.1 - v 0, p.2 - v 1]))
      = pure (p.1 * p.2) := by
    simp [PMF.monad_map_eq_map, PMF.monad_pure_eq_pure, PMF.map_bind, PMF.pure_map, PMF.bind_const]
  rw [out, pure_bind]
  simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  -- masks: `(a, b) ↦ (x - a, y - b)` is a bijection of `F²`, so the opened pair is uniform
  let e : (Fin 2 → F) ≃ F × F :=
    (piFinTwoEquiv fun _ => F).trans ((Equiv.subLeft p.1).prodCongr (Equiv.subLeft p.2))
  rw [PMF.bind_map, ← uniform_map_equiv e, PMF.bind_map]
  rfl
end BeaverPrivacy

end Examples
end Glean
