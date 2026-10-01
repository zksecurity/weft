import Weft
import Examples.Basic

/-!
# Privacy with a fixed public trace

Addition, subtraction and multiplication return shares without value disclosure.
Constants and scalar multiplication explicitly disclose their public operands.
Events record the operation and its declared leakage.
If this event list is independent of the secret input,
a simulator can replay it.

`arith_private` requires equality of the full view, including declared leakage.
Deterministic arithmetic alone does not imply this hypothesis.
-/
namespace Weft.Examples.Silent
open Weft.Examples.Basic

section
variable (F : Type) [Add F] [Mul F] [Sub F]

/-- Linear operations and multiplication alone. -/
abbrev Arith : Hybrid := [Const F, Addition F, Subtraction F, Smul F, Mult F]

/-- The arithmetic hybrid has deterministic semantics. -/
theorem arith_model : (Arith F).model = (Arith F).eval.lift PMF := by
  apply Hybrid.model_lift
  intro i
  match i with
  | ⟨0, _⟩ => exact Const.model_eq F
  | ⟨1, _⟩ => exact Addition.model_eq F
  | ⟨2, _⟩ => exact Subtraction.model_eq F
  | ⟨3, _⟩ => exact Smul.model_eq F
  | ⟨4, _⟩ => exact Mult.model_eq F
  | ⟨n + 5, h⟩ => exact absurd h (by simp)

/-- An input-independent view can be simulated by returning `ops`. -/
theorem arith_private {I α : Type} (c : I → Prog (Arith F).ops .ideal α) (ops : List (Event (Arith F).ops))
    (hview : ∀ i, view (Arith F).eval (c i) = ops) :
    ∃ Sim : PMF (List (Event (Arith F).ops)), ∀ i,
      dist (Arith F).model (c i) = (do let y ← pure (output (Arith F).eval (c i)); let s ← Sim; pure (y, s)) := by
  refine ⟨pure ops, fun i => ?_⟩
  rw [arith_model, dist_lift, hview i]
  simp

-- Evaluate the arithmetic result.
example (a b c : F) : output (Arith F).eval (mul3 (fs := Arith F) (D := .ideal) a b c) = a * b * c := rfl
-- The view consists of two multiplication records for every input.
example (a b c : F) : view (Arith F).eval (mul3 (fs := Arith F) (D := .ideal) a b c)
    = [⟨4, ()⟩, ⟨4, ()⟩] := rfl
end

end Weft.Examples.Silent
