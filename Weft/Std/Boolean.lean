import Weft.Std.Hybrids
import Mathlib.Data.ZMod.Basic

/-!
# Boolean circuits: the `𝔽₂` hybrid

`𝔽₂` is `ZMod 2`: `+` is xor, `*` is and.  A Boolean circuit is an
ordinary `Lin`/`Mult` program over `GF2`, and `Bool2` is the hybrid that
offers exactly those two.  Its usual price list makes xor free and one
AND one round and one unit, so `delayOn` is the AND depth and `commOn`
the AND count.
-/
namespace Weft

/-- `𝔽₂` is `ZMod 2`: `+` is xor, `*` is and, literals `0` and `1`. -/
abbrev GF2 := ZMod 2

namespace GF2

/-- A bit, as a natural number. -/
def toNat (c : GF2) : ℕ := c.val

/-- A Boolean as a bit. -/
def ofBool (b : Bool) : GF2 := if b then 1 else 0

/-- A bit as a Boolean. -/
def toBool (c : GF2) : Bool := decide (c = 1)

@[simp] theorem ofBool_true : ofBool true = 1 := rfl
@[simp] theorem ofBool_false : ofBool false = 0 := rfl
@[simp] theorem toBool_ofBool (b : Bool) : toBool (ofBool b) = b := by cases b <;> decide
@[simp] theorem ofBool_toBool (c : GF2) : ofBool (toBool c) = c := by
  revert c; decide
@[simp] theorem ofBool_xor (a b : Bool) : ofBool (a ^^ b) = ofBool a + ofBool b := by
  cases a <;> cases b <;> decide
@[simp] theorem ofBool_and (a b : Bool) : ofBool (a && b) = ofBool a * ofBool b := by
  cases a <;> cases b <;> decide
@[simp] theorem toNat_ofBool (b : Bool) : toNat (ofBool b) = b.toNat := by cases b <;> rfl
theorem toBool_add (a b : GF2) : toBool (a + b) = (toBool a ^^ toBool b) := by
  revert a b; decide
theorem toBool_mul (a b : GF2) : toBool (a * b) = (toBool a && toBool b) := by
  revert a b; decide
@[simp] theorem toBool_eq_true_iff (c : GF2) : toBool c = true ↔ c = 1 := by simp [toBool]
@[simp] theorem toBool_eq_false_iff (c : GF2) : toBool c = false ↔ c = 0 := by
  revert c; decide

end GF2

/-- The `m` low bits of `n` as elements of `𝔽₂`, least significant first. -/
def bitsOf (m : Nat) (n : Nat) : Fin m → GF2 := fun i => if n.testBit i then 1 else 0

/-- Boolean circuits: xor (free, `Lin`) and and (`Mult`). -/
abbrev Bool2 : Hybrid := [Lin GF2, Mult GF2]

namespace Bool2

/-- The operations, by position, for stating views. -/
abbrev lin (o : Lin.Op) : Bool2.ops.Op := ⟨0, o⟩
abbrev mult : Bool2.ops.Op := ⟨1, .mult⟩

/-- The Boolean MPC: xor free, an AND one round and one unit by default. -/
abbrev mpc (pMult : Price := ⟨1, 1⟩) : MPC := [(Lin GF2).priced ⟨0, 0⟩, (Mult GF2).priced pMult]

/-- The cost instantiation of Boolean circuits at that price. -/
def timed (pMult : Price := ⟨1, 1⟩) : Model Bool2.ops .timed Sched := (mpc pMult).timed

/-- No functionality of `Bool2` draws coins: its semantics is its evaluation model, lifted. -/
theorem model_eq : Bool2.model = Bool2.eval.lift PMF := by
  apply Hybrid.model_lift
  intro i
  match i with
  | ⟨0, _⟩ => exact Lin.model_eq GF2
  | ⟨1, _⟩ => exact Mult.model_eq GF2
  | ⟨n + 2, h⟩ => exact absurd h (by simp)

end Bool2

end Weft
