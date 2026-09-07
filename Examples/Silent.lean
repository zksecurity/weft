import Weft
import Examples.Basic

/-!
# Privacy with a fixed public trace

Linear operations and multiplication return shares without additional disclosure.
Their events still record the operation and clear operands.
If this event list is independent of the secret input,
a simulator can replay it.

`arith_private` requires equality of the full view, including clear operands.
Deterministic arithmetic alone does not imply this hypothesis.
-/
namespace Weft.Examples.Silent
open Weft.Examples.Basic

section
variable (F : Type) [Add F] [Mul F] [Sub F]

/-- Linear operations and multiplication alone. -/
abbrev Arith : Hybrid := [Lin F, Mult F]

/-- The arithmetic hybrid has deterministic semantics. -/
theorem arith_model : (Arith F).model = (Arith F).eval.lift PMF := by
  apply Model.ext
  intro r
  obtain ⟨⟨⟨_ | _ | n, h⟩, o⟩, a⟩ := r
  · simp only [Hybrid.model_step, Hybrid.eval_step, Model.lift_step, Hybrid.get, Lin.model_eq]
  · simp only [Hybrid.model_step, Hybrid.eval_step, Model.lift_step, Hybrid.get, Mult.model_eq]
  · exact absurd h (by simp)

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
    = [⟨⟨1, .mult⟩, ((), (), ()), (), ()⟩, ⟨⟨1, .mult⟩, ((), (), ()), (), ()⟩] := rfl
end

end Weft.Examples.Silent
