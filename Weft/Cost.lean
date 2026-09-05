import Weft.Realization

/-!
# Price lists, communication, and how cost composes

An MPC is what it charges: a list of functionalities, each with a price
per operation.  The same list gives membership (`Has`), semantics (the
hybrid's model) and pricing, so "the MPC offers `X`" is said once.  A
price sees the operation only, never an operand; constant pricing is the
special case.

Delay and communication are separate observables.  Communication is the
additive cost model of the price list, evaluated by the interpreter;
delay is the timed domain at the list's latencies.  Communication
composes exactly along realisations (`cost_handle`); delay under
dependency tracking is a conservative bound (`Weft.Timed`).
-/
namespace Weft

/-- The price of an operation on an MPC: its latency (rounds) and its
communication.  Latency feeds the timed domain, communication the additive
cost model. -/
structure Price where
  delay : Nat
  comm : Nat
  deriving DecidableEq, Repr

/-- A price list: functionalities, each priced per operation. -/
abbrev MPC := List ((F : Functionality) × (F.ops.Op → Price))

namespace MPC

/-- The hybrid an MPC offers.  Reducible and structurally recursive so
that `Has F M.hybrid` is found by instance search on a literal list. -/
@[reducible] def hybrid : MPC → Hybrid
  | [] => []
  | ⟨F, _⟩ :: M => F :: hybrid M

/-- The price of an operation of the hybrid, looked up at the same position `Has` finds. -/
def price : (M : MPC) → M.hybrid.ops.Op → Price
  | ⟨_, p⟩ :: _, ⟨⟨0, _⟩, o⟩ => p o
  | _ :: M, ⟨⟨n + 1, h⟩, o⟩ => price M ⟨⟨n, Nat.lt_of_succ_lt_succ h⟩, o⟩

/-- The semantics of the MPC's hybrid. -/
noncomputable abbrev model (M : MPC) : Model M.hybrid.ops .ideal PMF := M.hybrid.model
/-- The evaluation model of the MPC's hybrid. -/
abbrev eval (M : MPC) : Model M.hybrid.ops .ideal Id := M.hybrid.eval
/-- The communication cost model: derived, not chosen. -/
def comm (M : MPC) : CostModel M.hybrid.ops Nat := ⟨fun o => (M.price o).comm⟩
/-- The latency of each operation. -/
def latency (M : MPC) (o : M.hybrid.ops.Op) : Nat := (M.price o).delay
/-- The timed model of the MPC: each operation at the latency it charges. -/
def timed (M : MPC) : Model M.hybrid.ops .timed Sched := M.hybrid.timed M.latency

/-- A constant price for every operation of a functionality. -/
abbrev const (F : Functionality) (p : Price) : (F : Functionality) × (F.ops.Op → Price) := ⟨F, fun _ => p⟩

end MPC

/-! ## Cost as a distribution, and composition -/

/-- The cost of a run, as a distribution (a reactive program's shape may
depend on what it reveals). -/
noncomputable def costDist {ι : Interface} {D : Domain} {C α : Type} [AddMonoid C] (M : Model ι D PMF)
    (K : CostModel ι C) (c : Prog ι D α) : PMF C :=
  (fun r => r.2.cost) <$> run M K c

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
      have : q.2.cost ∈ (fun q : _ × Trace gs.ops C => q.2.cost) '' (run gs.model K (g.impl .ideal r)).support :=
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
