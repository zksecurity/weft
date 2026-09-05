import Weft.Prog
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Models and the interpreter

A model of an interface says, in a monad `m`, what each request does: one
joint *step* returning the response together with the declared disclosure.
The step is the authoritative joint law; the response marginal is
`program`, and there is no separate `leak` accessor, because the
correlation between response and disclosure is part of the specification
(a public coin whose value is disclosed but not returned).

Three monads matter:

* `PMF` is **the semantics**: a run is a distribution over (output, view).
* `Id` is **evaluation**: coin-free programs compute output, view and cost
  by `rfl`; randomised functionalities have an evaluation model with the
  coins fixed to a dummy.
* `Sched` (a clock state, `Weft.Timed`) is **scheduling**: delay.

The interpreter is written once, for any monad, and records one event per
request: the operation, the blanked response, and the sampled disclosure.
-/
namespace Weft

/-- A model: one joint step per request, in `m`. -/
structure Model (ι : Interface) (D : Domain) (m : Type → Type) where
  step : (r : Req ι D) → m (Resp ι D r.op × ι.disc r.op)

namespace Model
variable {ι : Interface} {D : Domain} {m : Type → Type}

/-- A deterministic step, seen in any monad. -/
def det [Monad m] (program : (r : Req ι D) → Resp ι D r.op)
    (leak : (r : Req ι D) → ι.disc r.op) : Model ι D m :=
  ⟨fun r => pure (program r, leak r)⟩

/-- A deterministic and silent step (every disclosure type must be `Unit`). -/
def silent [Monad m] (program : (r : Req ι D) → Resp ι D r.op)
    (h : ∀ o, ι.disc o = Unit := by intro o; rfl) : Model ι D m :=
  det program fun r => (h r.op).symm ▸ ()

/-- An evaluation model, seen in any monad. -/
def lift (m : Type → Type) [Monad m] (M : Model ι D Id) : Model ι D m :=
  ⟨fun r => pure (M.step r).run⟩

/-- The response marginal. -/
def program [Functor m] (M : Model ι D m) (r : Req ι D) : m (Resp ι D r.op) :=
  Prod.fst <$> M.step r

theorem ext {M N : Model ι D m} (h : ∀ r, M.step r = N.step r) : M = N := by
  cases M; cases N; simp only [Model.mk.injEq]; exact funext h

@[simp] theorem lift_step [Monad m] (M : Model ι D Id) (r : Req ι D) :
    (M.lift m).step r = pure (M.step r).run := rfl
@[simp] theorem det_step [Monad m] (program : (r : Req ι D) → Resp ι D r.op)
    (leak : (r : Req ι D) → ι.disc r.op) (r : Req ι D) :
    (det (m := m) program leak).step r = pure (program r, leak r) := rfl

end Model

/-- A cost model: a price for each operation, in an additive monoid.
Prices see operations only, never an operand. -/
structure CostModel (ι : Interface) (C : Type) where
  op : ι.Op → C

def CostModel.unit {ι : Interface} : CostModel ι Unit := ⟨fun _ => ()⟩

/-- What one run accumulates besides its result: cost and the view. -/
structure Trace (ι : Interface) (C : Type) where
  cost : C
  view : List (Event ι)

namespace Trace
variable {ι : Interface} {C : Type} [AddMonoid C]
def seq (t u : Trace ι C) : Trace ι C := ⟨t.cost + u.cost, t.view ++ u.view⟩
def zero : Trace ι C := ⟨0, []⟩
@[simp] theorem zero_view : (zero : Trace ι C).view = [] := rfl
@[simp] theorem zero_cost : (zero : Trace ι C).cost = 0 := rfl
@[simp] theorem seq_view (t u : Trace ι C) : (seq t u).view = t.view ++ u.view := rfl
@[simp] theorem seq_cost (t u : Trace ι C) : (seq t u).cost = t.cost + u.cost := rfl
@[simp] theorem zero_seq (t : Trace ι C) : seq zero t = t := by simp [seq, zero]
@[simp] theorem seq_zero (t : Trace ι C) : seq t zero = t := by simp [seq, zero]
@[simp] theorem seq_assoc (t u v : Trace ι C) : seq (seq t u) v = seq t (seq u v) := by
  simp [seq, add_assoc]
end Trace

/-- The interpreter: sample the step once, record the event, continue with
the sampled response. -/
def run {ι : Interface} {D : Domain} {C α : Type} [AddMonoid C] {m : Type → Type} [Monad m]
    (M : Model ι D m) (K : CostModel ι C) : Prog ι D α → m (α × Trace ι C)
  | .pure a => pure (a, Trace.zero)
  | .call r k => do
    let (y, d) ← M.step r
    let res ← run M K (k y)
    pure (res.1, Trace.seq ⟨K.op r.op, [⟨r.op, (ι.cod r.op).blank y, d⟩]⟩ res.2)

section Observables
variable {ι : Interface} {D : Domain} {C α : Type} [AddMonoid C]

/-- Evaluation (`m := Id`): the output of one run. -/
def output (M : Model ι D Id) (c : Prog ι D α) : α := (Id.run (run M CostModel.unit c)).1
/-- Evaluation: the view of one run. -/
def view (M : Model ι D Id) (c : Prog ι D α) : List (Event ι) := (Id.run (run M CostModel.unit c)).2.view
/-- Evaluation: the cost of one run. -/
def cost (M : Model ι D Id) (K : CostModel ι C) (c : Prog ι D α) : C := (Id.run (run M K c)).2.cost

/-- **The semantics** (`m := PMF`): the distribution of (output, view). -/
noncomputable def dist (M : Model ι D PMF) (c : Prog ι D α) : PMF (α × List (Event ι)) :=
  (fun p => (p.1, p.2.view)) <$> run M CostModel.unit c
end Observables

/-! ### The laws

`run_bind`: running a sequential composition is running the parts; it
holds in every lawful monad and is the only fact about the interpreter the
composition theorems need.  `run_lift`: a coin-free program under a lifted
model is a point, so `rfl` at `Id` is a theorem at `PMF`. -/

section Laws
variable {ι : Interface} {D : Domain} {C α β : Type} [AddMonoid C] {m : Type → Type} [Monad m]

@[simp] theorem run_pure (M : Model ι D m) (K : CostModel ι C) (a : α) :
    run M K (.pure a) = pure (a, Trace.zero) := rfl

theorem run_call (M : Model ι D m) (K : CostModel ι C) (r : Req ι D) (k : Resp ι D r.op → Prog ι D α) :
    run M K (.call r k) = (do
      let (y, d) ← M.step r
      let res ← run M K (k y)
      pure (res.1, Trace.seq ⟨K.op r.op, [⟨r.op, (ι.cod r.op).blank y, d⟩]⟩ res.2)) := rfl

/-- `>>=`, `pure` and `<$>` on `PMF` are Mathlib's `PMF.bind`, `PMF.pure`, `PMF.map`. -/
theorem PMF.monad_bind_eq_bind {α β : Type} (p : PMF α) (f : α → PMF β) : p >>= f = p.bind f := rfl
theorem PMF.monad_pure_eq_pure {α : Type} (a : α) : (pure a : PMF α) = PMF.pure a := rfl
theorem PMF.monad_map_eq_map {α β : Type} (f : α → β) (p : PMF α) : f <$> p = p.map f := rfl

variable [LawfulMonad m]

theorem run_bind (M : Model ι D m) (K : CostModel ι C) (c : Prog ι D α) (k : α → Prog ι D β) :
    run M K (Prog.bind c k) = (do
      let r ← run M K c
      let s ← run M K (k r.1)
      pure (s.1, Trace.seq r.2 s.2)) := by
  induction c with
  | pure a => simp [run]
  | call r k' ih => simp only [Prog.bind_call, run_call, ih, bind_assoc, pure_bind, Trace.seq_assoc]

theorem run_lift (M : Model ι D Id) (K : CostModel ι C) (c : Prog ι D α) :
    run (M.lift m) K c = pure (Id.run (run M K c)) := by
  induction c with
  | pure a => rfl
  | call r k ih =>
    simp only [run_call, ih, Model.lift_step]
    exact (pure_bind _ _).trans (by simp only [pure_bind]; rfl)

theorem dist_lift (M : Model ι D Id) (c : Prog ι D α) :
    dist (M.lift PMF) c = pure (output M c, view M c) := by
  simp [dist, run_lift, output, view]

theorem dist_pure (M : Model ι D PMF) (a : α) : dist M (.pure a) = pure (a, []) := by
  simp [dist]

theorem dist_call (M : Model ι D PMF) (r : Req ι D) (k : Resp ι D r.op → Prog ι D α) :
    dist M (.call r k) = (do
      let (y, d) ← M.step r
      let res ← dist M (k y)
      pure (res.1, ⟨r.op, (ι.cod r.op).blank y, d⟩ :: res.2)) := by
  simp [dist, run_call, Trace.seq]

theorem dist_bind (M : Model ι D PMF) (c : Prog ι D α) (k : α → Prog ι D β) :
    dist M (Prog.bind c k) = (do
      let r ← dist M c
      let s ← dist M (k r.1)
      pure (s.1, r.2 ++ s.2)) := by
  simp [dist, run_bind, Trace.seq]

/-- The result of a run does not depend on the cost model. -/
theorem run_fst (M : Model ι D m) {C' : Type} [AddMonoid C'] (K : CostModel ι C) (K' : CostModel ι C')
    (c : Prog ι D α) : Prod.fst <$> run M K c = Prod.fst <$> run M K' c := by
  induction c with
  | pure a => simp [run]
  | call r k ih => simp [run_call, ih]
end Laws

end Weft
