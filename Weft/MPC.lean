import Weft.Functionality
import Weft.Timed

/-!
# MPC cost models

An MPC pairs each functionality with a timed model of its single function.
`hybrid` determines ideal semantics and membership;
`timed` dispatches requests by functionality position.
`Functionality.priced` uses a fixed price per function.
`MPC.entry` accepts a custom timed model;
`MPC.derived` obtains one by running a realisation's implementation.
-/
namespace Weft

/-- A functionality paired with a timed model of its single function. -/
abbrev MPC.Entry := (F : Functionality) × FunctionModel F.sig .timed Sched

/-- A timed model for each functionality in a hybrid. -/
abbrev MPC := List MPC.Entry

namespace MPC

/-- The underlying hybrid. -/
@[reducible] def hybrid : MPC → Hybrid
  | [] => []
  | ⟨F, _⟩ :: M => F :: hybrid M

/-- Ideal semantics of the underlying hybrid. -/
noncomputable abbrev model (M : MPC) : Model M.hybrid.ops .ideal PMF := M.hybrid.model
/-- Deterministic evaluation of the underlying hybrid. -/
abbrev eval (M : MPC) : Model M.hybrid.ops .ideal Id := M.hybrid.eval

/-- Dispatch requests to the selected functionality's timed model. -/
def timed : (M : MPC) → Model M.hybrid.ops .timed Sched
  | [] => ⟨fun r => r.op.elim0⟩
  | ⟨_, T⟩ :: M => ⟨fun r => match r with
      | ⟨⟨0, _⟩, a⟩ => T.step a
      | ⟨⟨n + 1, h⟩, a⟩ => (timed M).step ⟨⟨n, Nat.lt_of_succ_lt_succ h⟩, a⟩⟩

@[simp] theorem timed_cons_zero (F : Functionality) (T : FunctionModel F.sig .timed Sched) (M : MPC)
    (a : F.sig.Args .timed) :
    (timed (⟨F, T⟩ :: M)).step ⟨Hybrid.head F M.hybrid, a⟩ = T.step a := rfl
@[simp] theorem timed_cons_succ (F : Functionality) (T : FunctionModel F.sig .timed Sched) (M : MPC)
    (i : Fin M.hybrid.length) (a : (M.hybrid.get i).sig.Args .timed) :
    (timed (⟨F, T⟩ :: M)).step ⟨Hybrid.next F M.hybrid i, a⟩ = M.timed.step ⟨i, a⟩ := rfl

/-- An MPC entry using a custom timed model. -/
abbrev entry (F : Functionality) (T : FunctionModel F.sig .timed Sched) : Entry := ⟨F, T⟩

end MPC

/-- Price a functionality's single function. -/
abbrev Functionality.priced (F : Functionality) (p : Price) : MPC.Entry := ⟨F, F.eval.timed p⟩

end Weft
