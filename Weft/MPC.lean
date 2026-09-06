import Weft.Functionality
import Weft.Timed

/-!
# An MPC: a hybrid instantiated in the cost model

A functionality is behaviour only.  An *MPC* is a hybrid with each
functionality instantiated in the cost model: a timed model of its
interface, which does the behaviour and pays the price (`Weft.Timed`).
The same list gives membership (`Has`), semantics (the hybrid's model)
and cost, so "the MPC offers `X`" is said once; two MPCs with the same
hybrid differ only in what they charge.

An entry is a functionality at a price (`(Mult F).priced ⟨1, 2⟩`, the
generic timed model of its interface), any timed model of the interface
at all (`MPC.entry`, a per-input profile for instance), or, for an
abstract operation that a realisation implements, the exact
instantiation that runs the implementation (`Realization.timed`,
`Weft.Cost`).
-/
namespace Weft

/-- One functionality, instantiated: the timed model its operations run in. -/
abbrev MPC.Entry := (F : Functionality) × Model F.ops .timed Sched

/-- An MPC: a hybrid, each functionality instantiated in the cost model. -/
abbrev MPC := List MPC.Entry

namespace MPC

/-- The hybrid an MPC offers.  Reducible and structurally recursive so
that `Has F M.hybrid` is found by instance search on a literal list. -/
@[reducible] def hybrid : MPC → Hybrid
  | [] => []
  | ⟨F, _⟩ :: M => F :: hybrid M

/-- The semantics of the MPC's hybrid: the functionalities' models, untouched. -/
noncomputable abbrev model (M : MPC) : Model M.hybrid.ops .ideal PMF := M.hybrid.model
/-- The evaluation model of the MPC's hybrid. -/
abbrev eval (M : MPC) : Model M.hybrid.ops .ideal Id := M.hybrid.eval

/-- The cost instantiation of the hybrid: dispatch by position to the entry's timed model. -/
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

/-- A functionality at a price per operation, by the generic timed model. -/
abbrev Functionality.pricedBy (F : Functionality) (p : F.ops.Op → Price) : MPC.Entry := ⟨F, Model.timed F.eval p⟩
/-- A functionality at one price for all of its operations. -/
abbrev Functionality.priced (F : Functionality) (p : Price) : MPC.Entry := F.pricedBy fun _ => p

end Weft
