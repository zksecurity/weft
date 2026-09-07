import Weft.Functionality
import Weft.Timed

/-!
# MPC cost models

An MPC pairs each functionality in a hybrid with a timed model.
`hybrid` determines the ideal semantics and membership instances;
`timed` dispatches requests to the corresponding timed models.

`Functionality.priced` uses a fixed operation price.
`MPC.entry` accepts a custom timed model,
and `MPC.derived` runs a realisation's implementation (`Weft.Cost`).
-/
namespace Weft

/-- A functionality paired with a timed model of its interface. -/
abbrev MPC.Entry := (F : Functionality) × Model F.ops .timed Sched

/-- A hybrid with a timed model for each component. -/
abbrev MPC := List MPC.Entry

namespace MPC

/-- The underlying hybrid.
Reducibility allows `Has` instance search on literal MPC lists. -/
@[reducible] def hybrid : MPC → Hybrid
  | [] => []
  | ⟨F, _⟩ :: M => F :: hybrid M

/-- Ideal semantics of the underlying hybrid. -/
noncomputable abbrev model (M : MPC) : Model M.hybrid.ops .ideal PMF := M.hybrid.model
/-- The evaluation model of the MPC's hybrid. -/
abbrev eval (M : MPC) : Model M.hybrid.ops .ideal Id := M.hybrid.eval

/-- Dispatch each request to its component's timed model. -/
def timed : (M : MPC) → Model M.hybrid.ops .timed Sched
  | [] => ⟨fun r => r.op.1.elim0⟩
  | ⟨_, T⟩ :: M => ⟨fun r => match r with
      | ⟨⟨⟨0, _⟩, o⟩, a⟩ => T.step ⟨o, a⟩
      | ⟨⟨⟨n + 1, h⟩, o⟩, a⟩ => (timed M).step ⟨⟨⟨n, Nat.lt_of_succ_lt_succ h⟩, o⟩, a⟩⟩

@[simp] theorem timed_cons_zero (F : Functionality) (T : Model F.ops .timed Sched) (M : MPC) (o : F.ops.Op)
    (a : Operands .timed (F.ops.dom o)) :
    (timed (⟨F, T⟩ :: M)).step ⟨⟨Hybrid.head F M.hybrid, o⟩, a⟩ = T.step ⟨o, a⟩ := rfl
@[simp] theorem timed_cons_succ (F : Functionality) (T : Model F.ops .timed Sched) (M : MPC) (i : Fin M.hybrid.length)
    (o : (M.hybrid.get i).ops.Op) (a : Operands .timed ((M.hybrid.get i).ops.dom o)) :
    (timed (⟨F, T⟩ :: M)).step ⟨⟨Hybrid.next F M.hybrid i, o⟩, a⟩ = (timed M).step ⟨⟨i, o⟩, a⟩ := rfl

/-- An entry from any timed model of the functionality's interface. -/
abbrev entry (F : Functionality) (T : Model F.ops .timed Sched) : Entry := ⟨F, T⟩

end MPC

/-- Price each operation using `Model.timed`. -/
abbrev Functionality.pricedBy (F : Functionality) (p : F.ops.Op → Price) : MPC.Entry := ⟨F, Model.timed F.eval p⟩
/-- Use one price for every operation of the functionality. -/
abbrev Functionality.priced (F : Functionality) (p : Price) : MPC.Entry := F.pricedBy fun _ => p

end Weft
