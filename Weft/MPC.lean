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

An entry is written with the hand-written timed model of a standard
interface (`Lin.priced F p`, `Mult.priced F p`, ...), with any timed model
at all (`MPC.entry`), or, for an abstract operation that a realisation
implements, with the exact instantiation that runs the implementation
(`Realization.timed`, `Weft.Cost`).  `MPC.const` uses the generic timed
model and is too slow to evaluate; it is the specification of the others.
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

/-- An entry from any timed model of the functionality's interface. -/
abbrev entry (F : Functionality) (T : Model F.ops .timed Sched) : Entry := ⟨F, T⟩

/-- An entry at a constant price, by the generic timed model: exact, and
too slow to evaluate; prefer the interface's hand-written model. -/
abbrev const (F : Functionality) (p : Price) : Entry := ⟨F, Model.timed F.eval fun _ => p⟩

end MPC

end Weft
