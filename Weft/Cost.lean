import Weft.Realization

/-!
# How cost composes

Two composition theorems for cost, both along realisations.

* **Exactly, in the cost model.**  The instantiation of an abstract
  operation under a realisation is to run the implementation in the
  target's timed model (`Realization.timed`).  With every abstract
  operation instantiated that way, a scheduled run of the caller in the
  hybrid *is* the scheduled run of the inlined program: same output,
  same clocks, same communication (`Realizations.run_timed`).  Delay and
  communication of a program written against abstract operations are
  then computed once, in the hybrid, and are what the instantiated
  program costs.  A hand-written model of the abstract operation (one
  latency, a per-input profile) is an approximation of this one; what it
  approximates is now a definition, not a claim.

* **As a distribution, in the ideal domain.**  For a reactive program the
  cost is a distribution; inlining priced realisations into a valid
  caller costs what the caller costs with each abstract operation priced
  at its implementation's cost (`cost_handle`).
-/
namespace Weft

/-! ## The exact instantiation of an abstract operation -/

/-- The timed model of `F` that runs `f`'s implementation in the timed
model `T` of the target: exact by construction. -/
def Realization.timed {F : Functionality} {fs : Hybrid} (f : Realization F fs) (T : Model fs.ops .timed Sched) :
    Model F.ops .timed Sched where
  step r := do
    let p ← run T CostModel.unit (f.impl .timed r)
    pure (p.1, (F.eval.step ⟨r.op, (F.ops.dom r.op).untime r.args⟩).run.2)

/-- The MPC entry for `F` instantiated by `f` over the MPC `M`. -/
abbrev MPC.derived (M : MPC) {F : Functionality} (f : Realization F M.hybrid) : MPC.Entry :=
  ⟨F, f.timed M.timed⟩

/-- The same for every component of a hybrid at once. -/
def Realizations.timed {fs gs : Hybrid} (g : Realizations fs gs) (T : Model gs.ops .timed Sched) :
    Model fs.ops .timed Sched where
  step r := do
    let p ← run T CostModel.unit (g.impl .timed r)
    pure (p.1, (fs.eval.step ⟨r.op, (fs.ops.dom r.op).untime r.args⟩).run.2)

/-- The output of a run, in the monad, with the trace dropped. -/
def runOut {ι : Interface} {D : Domain} {α : Type} {m : Type → Type} [Monad m] [Look D m] (M : Model ι D m)
    (c : Prog ι D α) : m α :=
  Prod.fst <$> run M CostModel.unit c

/-- **Composition, exactly.**  A scheduled run of the caller with every
abstract operation instantiated by its implementation is the scheduled
run of the inlined program. -/
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

theorem Realizations.commOn_timed {fs gs : Hybrid} (g : Realizations fs gs) (T : Model gs.ops .timed Sched)
    {α : Type} (c : Prog fs.ops .timed α) :
    commOn (g.timed T) c = commOn T (Prog.handle (g.impl .timed) c) := by
  simp [commOn, g.sched_timed T c]

/-! ## Cost as a distribution, and composition -/

/-- The cost of a run, as a distribution (a reactive program's shape may
depend on what it reveals). -/
noncomputable def costDist {ι : Interface} {D : Domain} {C α : Type} [AddMonoid C] [Look D PMF] (M : Model ι D PMF)
    (K : CostModel ι C) (c : Prog ι D α) : PMF C :=
  (fun r => r.2.cost) <$> run M K c

theorem costDist_look {ι : Interface} {C α T : Type} [AddMonoid C] (M : Model ι .ideal PMF) (K : CostModel ι C)
    (c : Domain.ideal.clear T) (k : T → Prog ι .ideal α) : costDist M K (.look c k) = costDist M K (k c) := by
  simp [costDist, run_look_ideal]

/-- A handler is *priced* under `K` if each request's program has a cost
independent of its operands and coins (structurally scheduled), given by `p`. -/
def Priced {ι κ : Interface} {C : Type} [AddMonoid C] (M : Model ι .ideal PMF)
    (impl : (r : Req κ .ideal) → Prog ι .ideal (Resp κ .ideal r.op)) (K : CostModel ι C) (p : CostModel κ C) :
    Prop :=
  ∀ r, costDist M K (impl r) = pure (p.op r.op)

/-- **Composition, communication.**  Inlining priced realisations into a
valid caller costs what the caller costs with each abstract operation
priced at its implementation's cost. -/
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
    -- the implementation's result is distributed as the abstract program's
    have fst : Prod.fst <$> run gs.model K (g.impl .ideal r) = Prod.fst <$> fs.model.step r := by
      rw [run_fst gs.model K CostModel.unit]
      have := congrArg (fun d => Prod.fst <$> d) (g.real r hr)
      simpa [dist, PMF.monad_map_eq_map, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.map,
        Function.comp_def, PMF.bind_bind, PMF.pure_bind, PMF.bind_const, PMF.bind_pure] using this
    -- ...and its cost is `p r.op` on the whole support
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
