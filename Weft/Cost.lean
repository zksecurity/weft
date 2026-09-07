import Weft.Realization

/-!
# Cost under composition

`Realization.timed` runs an implementation in the target's timed model.
`Realizations.runOut_timed` shows that using these derived models agrees with inlining:
the output, final clock and communication counter are equal.
Custom prices or profiles require a separate argument to bound this derived cost.

In the ideal domain, reactive programs can have random costs.
`cost_handle` gives equality of cost distributions for valid callers,
provided each implementation has a fixed cost for its abstract operation.
-/
namespace Weft

/-! ## Derived timed models -/

/-- Run `f`'s implementation under `T` to obtain a timed model of `F`. -/
def Realization.timed {F : Functionality} {fs : Hybrid} (f : Realization F fs) (T : Model fs.ops .timed Sched) :
    Model F.ops .timed Sched where
  step r := do
    let p ← run T CostModel.unit (f.impl .timed r)
    pure (p.1, (F.eval.step ⟨r.op, r.args.untime⟩).run.2)

/-- The MPC entry for `F` instantiated by `f` over the MPC `M`. -/
abbrev MPC.derived (M : MPC) {F : Functionality} (f : Realization F M.hybrid) : MPC.Entry :=
  ⟨F, f.timed M.timed⟩

/-- Derive a timed model for each component's implementation. -/
def Realizations.timed {fs gs : Hybrid} (g : Realizations fs gs) (T : Model gs.ops .timed Sched) :
    Model fs.ops .timed Sched where
  step r := do
    let p ← run T CostModel.unit (g.impl .timed r)
    pure (p.1, (fs.eval.step ⟨r.op, r.args.untime⟩).run.2)

/-- Project the output while preserving the monad's effects. -/
def runOut {ι : Interface} {D : Domain} {α : Type} {m : Type → Type} [Monad m] [Look D m] (M : Model ι D m)
    (c : Prog ι D α) : m α :=
  Prod.fst <$> run M CostModel.unit c

/-- Running under derived timed models agrees with inlining the implementations. -/
theorem Realizations.runOut_timed {fs gs : Hybrid} (g : Realizations fs gs) (T : Model gs.ops .timed Sched)
    {α : Type} (c : Prog fs.ops .timed α) :
    runOut (g.timed T) c = runOut T (Prog.handle (g.impl .timed) c) := by
  induction c with
  | pure a => simp [runOut, Prog.handle]
  | look c k ih =>
    simp only [runOut, Prog.handle_look, run_look, map_bind] at ih ⊢
    exact bind_congr fun v => ih v
  | call r k ih =>
    simp only [runOut, Prog.handle_call, run_bind, run_call, Realizations.timed, map_bind, bind_assoc, pure_bind,
      map_pure] at ih ⊢
    refine bind_congr fun a => ?_
    have := ih a.1
    simpa only [map_eq_pure_bind, Function.comp_def] using this

/-- Run one component's implementation and record the abstract request's event. -/
theorem Realizations.run_opAt {fs gs : Hybrid} (g : Realizations fs gs) (T : Model gs.ops .timed Sched)
    (i : Fin fs.length) (r : Req (fs.get i).ops .timed) (s : Clock) :
    StateT.run (run (g.timed T) CostModel.unit (Prog.opAt fs i r)) s =
      (((StateT.run (run T CostModel.unit ((g.get i).impl .timed r)) s).1.1,
        ⟨(), [⟨⟨i, r.op⟩, r.args.blank,
          ((fs.get i).ops.cod r.op).blank (StateT.run (run T CostModel.unit ((g.get i).impl .timed r)) s).1.1,
          ((fs.get i).eval.step ⟨r.op, r.args.untime⟩).run.2⟩]⟩),
       (StateT.run (run T CostModel.unit ((g.get i).impl .timed r)) s).2) := by
  simp only [Prog.opAt, run_call, run_pure, Realizations.timed, Realizations.impl, StateT.run_bind, StateT.run_pure,
    Trace.seq, Trace.zero]
  rfl

@[simp] theorem Realizations.get_cons_zero {F : Functionality} {fs gs : Hybrid} (r : Realization F gs)
    (rs : Realizations fs gs) : Realizations.get (.cons r rs) ⟨0, Nat.zero_lt_succ _⟩ = r := rfl
@[simp] theorem Realizations.get_cons_succ {F : Functionality} {fs gs : Hybrid} (r : Realization F gs)
    (rs : Realizations fs gs) (n : Nat) (h : n + 1 < (F :: fs).length) :
    Realizations.get (.cons r rs) ⟨n + 1, h⟩ = rs.get ⟨n, Nat.lt_of_succ_lt_succ h⟩ := rfl

theorem Realizations.sched_timed {fs gs : Hybrid} (g : Realizations fs gs) (T : Model gs.ops .timed Sched)
    {α : Type} (c : Prog fs.ops .timed α) :
    Sched.run (g.timed T) c = Sched.run T (Prog.handle (g.impl .timed) c) := by
  have h := congrArg (fun x : Sched α => StateT.run x {}) (g.runOut_timed T c)
  simp only [runOut, StateT.run_map] at h
  exact h

theorem Realizations.delayOn_timed {fs gs : Hybrid} (g : Realizations fs gs) (T : Model gs.ops .timed Sched)
    {X : Type} (c : Prog fs.ops .timed (Timed X)) :
    delayOn (g.timed T) c = delayOn T (Prog.handle (g.impl .timed) c) := by
  simp [delayOn, g.sched_timed T c]

theorem Realizations.readyOn_timed {fs gs : Hybrid} (g : Realizations fs gs) (T : Model gs.ops .timed Sched)
    (s : Shape) (c : Prog fs.ops .timed (s.interp .timed)) :
    readyOn (g.timed T) s c = readyOn T s (Prog.handle (g.impl .timed) c) := by
  simp [readyOn, g.sched_timed T c]

theorem Realizations.commOn_timed {fs gs : Hybrid} (g : Realizations fs gs) (T : Model gs.ops .timed Sched)
    {α : Type} (c : Prog fs.ops .timed α) :
    commOn (g.timed T) c = commOn T (Prog.handle (g.impl .timed) c) := by
  simp [commOn, g.sched_timed T c]

/-! ## Cost distributions -/

/-- Cost distribution, including variation caused by public control flow. -/
noncomputable def costDist {ι : Interface} {D : Domain} {C α : Type} [AddMonoid C] [Look D PMF] (M : Model ι D PMF)
    (K : CostModel ι C) (c : Prog ι D α) : PMF C :=
  (fun r => r.2.cost) <$> run M K c

theorem costDist_look {ι : Interface} {C α T : Type} [AddMonoid C] (M : Model ι .ideal PMF) (K : CostModel ι C)
    (c : Domain.ideal.clear T) (k : T → Prog ι .ideal α) : costDist M K (.look c k) = costDist M K (k c) := by
  simp [costDist, run_look_ideal]

/-- Every implementation run costs `p` for its operation,
independently of operands and random coins. -/
def Priced {ι κ : Interface} {C : Type} [AddMonoid C] (M : Model ι .ideal PMF)
    (impl : (r : Req κ .ideal) → Prog ι .ideal (Resp κ .ideal r.op)) (K : CostModel ι C) (p : CostModel κ C) :
    Prop :=
  ∀ r, costDist M K (impl r) = pure (p.op r.op)

/-- Inlining preserves the cost distribution when abstract prices match implementation costs. -/
theorem cost_handle {fs gs : Hybrid} {C : Type} [AddMonoid C] (g : Realizations fs gs)
    {K : CostModel gs.ops C} {p : CostModel fs.ops C} (hp : Priced gs.model (g.impl .ideal) K p)
    {α : Type} (c : Prog fs.ops .ideal α) (hc : Valid fs.model g.Pre c) :
    costDist gs.model K (Prog.handle (g.impl .ideal) c) = costDist fs.model p c := by
  induction c with
  | pure a => simp [Prog.handle, costDist, run]
  | look c k ih =>
    cases hc with
    | look _ _ hk => rw [Prog.handle_look, costDist_look, costDist_look]; exact ih c hk
  | call r k ih =>
    cases hc with
    | call _ _ hr hk =>
    -- The realisation equation gives equality of response marginals.
    have fst : Prod.fst <$> run gs.model K (g.impl .ideal r) = Prod.fst <$> fs.model.step r := by
      rw [run_fst gs.model K CostModel.unit]
      have := congrArg (fun d => Prod.fst <$> d) (g.real r hr)
      simpa [dist, PMF.monad_map_eq_map, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.map,
        Function.comp_def, PMF.bind_bind, PMF.pure_bind, PMF.bind_const, PMF.bind_pure] using this
    -- Every supported implementation run has cost `p.op r.op`.
    have cst : ∀ q ∈ (run gs.model K (g.impl .ideal r)).support, q.2.cost = p.op r.op := by
      intro q hq
      have := hp r
      simp only [costDist, PMF.monad_map_eq_map, PMF.monad_pure_eq_pure] at this
      have := congrArg PMF.support this
      rw [PMF.support_map, PMF.support_pure] at this
      have : q.2.cost ∈ (fun q : _ × Trace gs.ops .ideal C => q.2.cost) '' (run gs.model K (g.impl .ideal r)).support :=
        ⟨q, hq, rfl⟩
      simpa [*] using this
    rw [Prog.handle_call, costDist, run_bind]
    simp only [costDist, run_call, PMF.monad_map_eq_map, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
      PMF.map_bind, PMF.pure_map] at ih ⊢
    rw [PMF.bind_congr_support (g := fun q => (run gs.model K (Prog.handle (g.impl .ideal) (k q.1))).bind fun s =>
      PMF.pure (p.op r.op + s.2.cost)) (fun q hq => by simp [Trace.seq, cst q hq])]
    have e : ((run gs.model K (g.impl .ideal r)).bind fun q =>
          (run gs.model K (Prog.handle (g.impl .ideal) (k q.1))).bind fun s => PMF.pure (p.op r.op + s.2.cost))
        = (Prod.fst <$> run gs.model K (g.impl .ideal r)).bind fun y =>
          (run gs.model K (Prog.handle (g.impl .ideal) (k y))).bind fun s => PMF.pure (p.op r.op + s.2.cost) := by
      simp [PMF.monad_map_eq_map, PMF.bind_map, Function.comp_def]
    rw [e, fst]
    simp only [PMF.monad_map_eq_map, PMF.bind_map, Function.comp_def]
    refine PMF.bind_congr_support fun z hz => ?_
    have := ih z.1 (hk z hz)
    calc ((run gs.model K (Prog.handle (g.impl .ideal) (k z.1))).bind fun s => PMF.pure (p.op r.op + s.2.cost))
        = ((run gs.model K (Prog.handle (g.impl .ideal) (k z.1))).map fun s => s.2.cost).bind fun c =>
            PMF.pure (p.op r.op + c) := by
          simp [PMF.bind_map, Function.comp_def]
      _ = ((run fs.model p (k z.1)).map fun s => s.2.cost).bind fun c => PMF.pure (p.op r.op + c) := by rw [this]
      _ = _ := by simp [PMF.bind_map, Function.comp_def, Trace.seq]

end Weft
