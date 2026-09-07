import Weft.Prog
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Models and the interpreter

A model gives each request a joint response and disclosure in a monad `m`.
Sampling them together preserves their correlation,
e.g. when a public coin affects the response.
`Model.program` projects the response marginal.

`PMF` gives probabilistic semantics; `Id` gives deterministic evaluation.
For randomised functionalities, the evaluation model fixes the coins.
`Sched` adds timing and communication accounting (`Weft.Timed`).

`run` interprets a program and records one event per request.
-/
namespace Weft

/-- A joint response and disclosure for each request. -/
structure Model (ι : Interface) (D : Domain) (m : Type → Type) where
  step : (r : Req ι D) → m (Resp ι D r.op × ι.leak r.op)

namespace Model
variable {ι : Interface} {D : Domain} {m : Type → Type}

/-- Embed deterministic responses and disclosures in `m`. -/
def det [Monad m] (program : (r : Req ι D) → Resp ι D r.op)
    (leak : (r : Req ι D) → ι.leak r.op) : Model ι D m :=
  ⟨fun r => pure (program r, leak r)⟩

/-- A deterministic model with no declared disclosure.
Operations and clear values are still recorded by the interpreter. -/
def silent [Monad m] (program : (r : Req ι D) → Resp ι D r.op)
    (h : ∀ o, ι.leak o = Unit := by intro o; rfl) : Model ι D m :=
  det program fun r => (h r.op).symm ▸ ()

/-- Embed an evaluation model in `m`. -/
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
    (leak : (r : Req ι D) → ι.leak r.op) (r : Req ι D) :
    (det (m := m) program leak).step r = pure (program r, leak r) := rfl

end Model

/-- Interpret a clear-value read in `m`.
The ideal instance returns the value;
the timed instance also waits until it is available. -/
class Look (D : Domain) (m : Type → Type) where
  look : {T : Type} → D.clear T → m T

instance {m : Type → Type} [Monad m] : Look .ideal m := ⟨fun c => pure c⟩

@[simp] theorem Look.ideal_look {m : Type → Type} [Monad m] {T : Type} (c : Domain.ideal.clear T) :
    (Look.look c : m T) = pure c := rfl

/-- Additive cost indexed by operation, independent of operands. -/
structure CostModel (ι : Interface) (C : Type) where
  op : ι.Op → C

def CostModel.unit {ι : Interface} : CostModel ι Unit := ⟨fun _ => ()⟩

/-- Accumulated cost and adversarial view. -/
structure Trace (ι : Interface) (D : Domain) (C : Type) where
  cost : C
  view : List (Event ι D)

namespace Trace
variable {ι : Interface} {D : Domain} {C : Type} [AddMonoid C]
def seq (t u : Trace ι D C) : Trace ι D C := ⟨t.cost + u.cost, t.view ++ u.view⟩
def zero : Trace ι D C := ⟨0, []⟩
@[simp] theorem zero_view : (zero : Trace ι D C).view = [] := rfl
@[simp] theorem zero_cost : (zero : Trace ι D C).cost = 0 := rfl
@[simp] theorem seq_view (t u : Trace ι D C) : (seq t u).view = t.view ++ u.view := rfl
@[simp] theorem seq_cost (t u : Trace ι D C) : (seq t u).cost = t.cost + u.cost := rfl
@[simp] theorem zero_seq (t : Trace ι D C) : seq zero t = t := by simp [seq, zero]
@[simp] theorem seq_zero (t : Trace ι D C) : seq t zero = t := by simp [seq, zero]
@[simp] theorem seq_assoc (t u v : Trace ι D C) : seq (seq t u) v = seq t (seq u v) := by
  simp [seq, add_assoc]
end Trace

/-- Sample each step and record its event before running the continuation.
Use projections for the sampled pair;
pattern matching here causes exponential reduction time under `rfl`. -/
def run {ι : Interface} {D : Domain} {C α : Type} [AddMonoid C] {m : Type → Type} [Monad m] [Look D m]
    (M : Model ι D m) (K : CostModel ι C) : Prog ι D α → m (α × Trace ι D C)
  | .pure a => pure (a, Trace.zero)
  | .call r k => do
    let p ← M.step r
    let res ← run M K (k p.1)
    pure (res.1, Trace.seq ⟨K.op r.op, [⟨r.op, r.args.blank, (ι.cod r.op).blank p.1, p.2⟩]⟩ res.2)
  | .look c k => do
    let v ← Look.look c
    run M K (k v)

section Observables
variable {ι : Interface} {D : Domain} {C α : Type} [AddMonoid C] [Look D Id] [Look D PMF]

/-- Evaluation (`m := Id`): the output of one run. -/
def output (M : Model ι D Id) (c : Prog ι D α) : α := (Id.run (run M CostModel.unit c)).1
/-- Evaluation: the view of one run. -/
def view (M : Model ι D Id) (c : Prog ι D α) : List (Event ι D) := (Id.run (run M CostModel.unit c)).2.view
/-- Evaluation: the cost of one run. -/
def cost (M : Model ι D Id) (K : CostModel ι C) (c : Prog ι D α) : C := (Id.run (run M K c)).2.cost

/-- The joint distribution of output and adversarial view. -/
noncomputable def dist (M : Model ι D PMF) (c : Prog ι D α) : PMF (α × List (Event ι D)) :=
  (fun p => (p.1, p.2.view)) <$> run M CostModel.unit c
end Observables

/-! ### Interpreter laws

`run_bind` decomposes a sequential run and concatenates its traces.
`run_lift` identifies a run under a lifted evaluation model with a point mass. -/

section Laws
variable {ι : Interface} {D : Domain} {C α β : Type} [AddMonoid C] {m : Type → Type} [Monad m] [Look D m] [Look D PMF]

omit [Look D PMF] in
@[simp] theorem run_pure (M : Model ι D m) (K : CostModel ι C) (a : α) :
    run M K (.pure a) = pure (a, Trace.zero) := rfl

omit [Look D PMF] in
theorem run_call (M : Model ι D m) (K : CostModel ι C) (r : Req ι D) (k : Resp ι D r.op → Prog ι D α) :
    run M K (.call r k) = (do
      let p ← M.step r
      let res ← run M K (k p.1)
      pure (res.1, Trace.seq ⟨K.op r.op, [⟨r.op, r.args.blank, (ι.cod r.op).blank p.1, p.2⟩]⟩ res.2)) := rfl

omit [Look D PMF] in
theorem run_look (M : Model ι D m) (K : CostModel ι C) {T : Type} (c : D.clear T) (k : T → Prog ι D α) :
    run M K (.look c k) = (do let v ← Look.look c; run M K (k v)) := rfl

/-- `>>=`, `pure` and `<$>` on `PMF` are Mathlib's `PMF.bind`, `PMF.pure`, `PMF.map`. -/
theorem PMF.monad_bind_eq_bind {α β : Type} (p : PMF α) (f : α → PMF β) : p >>= f = p.bind f := rfl
theorem PMF.monad_pure_eq_pure {α : Type} (a : α) : (pure a : PMF α) = PMF.pure a := rfl
theorem PMF.monad_map_eq_map {α β : Type} (f : α → β) (p : PMF α) : f <$> p = p.map f := rfl

variable [LawfulMonad m]

omit [Look D PMF] in
theorem run_bind (M : Model ι D m) (K : CostModel ι C) (c : Prog ι D α) (k : α → Prog ι D β) :
    run M K (Prog.bind c k) = (do
      let r ← run M K c
      let s ← run M K (k r.1)
      pure (s.1, Trace.seq r.2 s.2)) := by
  induction c with
  | pure a => simp [run]
  | call r k' ih => simp only [Prog.bind_call, run_call, ih, bind_assoc, pure_bind, Trace.seq_assoc]
  | look c k' ih => simp only [Prog.bind_look, run_look, ih, bind_assoc]

/-- An ideal-domain read applies the continuation without an effect. -/
theorem run_look_ideal (M : Model ι .ideal m) (K : CostModel ι C) {T : Type} (c : Domain.ideal.clear T)
    (k : T → Prog ι .ideal α) : run M K (.look c k) = run M K (k c) := by
  simp [run_look]

theorem run_lift (M : Model ι .ideal Id) (K : CostModel ι C) (c : Prog ι .ideal α) :
    run (M.lift m) K c = pure (Id.run (run M K c)) := by
  induction c with
  | pure a => rfl
  | call r k ih =>
    simp only [run_call, ih, Model.lift_step]
    exact (pure_bind _ _).trans (by simp only [pure_bind]; rfl)
  | look c k ih => simp only [run_look_ideal, ih]

theorem dist_lift (M : Model ι .ideal Id) (c : Prog ι .ideal α) :
    dist (M.lift PMF) c = pure (output M c, view M c) := by
  simp [dist, run_lift, output, view]

theorem dist_look (M : Model ι .ideal PMF) {T : Type} (c : Domain.ideal.clear T) (k : T → Prog ι .ideal α) :
    dist M (.look c k) = dist M (k c) := by
  simp [dist, run_look_ideal]

theorem dist_pure (M : Model ι D PMF) (a : α) : dist M (.pure a) = pure (a, []) := by
  simp [dist]

theorem dist_pure' (M : Model ι D PMF) (a : α) : dist M (pure a) = pure (a, []) := dist_pure M a

theorem dist_call (M : Model ι D PMF) (r : Req ι D) (k : Resp ι D r.op → Prog ι D α) :
    dist M (.call r k) = (do
      let p ← M.step r
      let res ← dist M (k p.1)
      pure (res.1, ⟨r.op, r.args.blank, (ι.cod r.op).blank p.1, p.2⟩ :: res.2)) := by
  simp [dist, run_call, Trace.seq]

theorem dist_bind (M : Model ι D PMF) (c : Prog ι D α) (k : α → Prog ι D β) :
    dist M (Prog.bind c k) = (do
      let r ← dist M c
      let s ← dist M (k r.1)
      pure (s.1, r.2 ++ s.2)) := by
  simp [dist, run_bind, Trace.seq]

omit [Look D PMF] in
/-- The result of a run does not depend on the cost model. -/
theorem run_fst (M : Model ι D m) {C' : Type} [AddMonoid C'] (K : CostModel ι C) (K' : CostModel ι C')
    (c : Prog ι D α) : Prod.fst <$> run M K c = Prod.fst <$> run M K' c := by
  induction c with
  | pure a => simp [run]
  | call r k ih => simp [run_call, ih]
  | look c k ih => simp [run_look, ih]
end Laws

/-! ### Evaluation of a sequential composition -/

section Eval
variable {ι : Interface} {D : Domain} {α β : Type} [Look D Id]

/-- Evaluate the continuation on the first program's output. -/
theorem output_bind (M : Model ι D Id) (c : Prog ι D α) (k : α → Prog ι D β) :
    output M (Prog.bind c k) = output M (k (output M c)) := by
  simp only [output, run_bind]
  rfl

/-- Concatenate the first program's view with the continuation's view. -/
theorem view_bind (M : Model ι D Id) (c : Prog ι D α) (k : α → Prog ι D β) :
    view M (Prog.bind c k) = view M c ++ view M (k (output M c)) := by
  simp only [view, output, run_bind]
  rfl

@[simp] theorem output_pure (M : Model ι D Id) (a : α) : output M (.pure a) = a := rfl
@[simp] theorem view_pure (M : Model ι D Id) (a : α) : view M (.pure a) = [] := rfl
end Eval

end Weft
