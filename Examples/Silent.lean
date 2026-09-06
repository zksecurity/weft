import Weft
import Examples.Basic

/-!
# Sanity check: with only `add` and `mul`, privacy needs a public-trace hypothesis

Over a hybrid whose functionalities declare nothing and return only
shares, the adversary's view of a run is the sequence of operations
(with their clear arguments) and nothing else.  Such a program realises
"its own output distribution with no disclosure" exactly when that
sequence is a function of public data alone: a *straight-line* program
has a view that does not depend on its operands, and the simulator replays
it.  The old `hiding_of_silent` had no such hypothesis and was too strong:
a program whose shape depends on a share's value at the ideal domain has
different views for different inputs (report, Issue 3; `shapeLeak`).
-/
namespace Weft.Examples.Silent
open Weft.Examples.Basic

section
variable (F : Type) [Add F] [Mul F] [Sub F]

/-- Linear operations and multiplication alone. -/
abbrev Arith : Hybrid := [Lin F, Mult F]

/-- No functionality of the hybrid draws coins: the semantics is the evaluation model, lifted. -/
theorem arith_model : (Arith F).model = (Arith F).eval.lift PMF := by
  apply Model.ext
  intro r
  obtain ⟨⟨⟨_ | _ | n, h⟩, o⟩, a⟩ := r
  · simp only [Hybrid.model_step, Hybrid.eval_step, Model.lift_step, Hybrid.get, Lin.model_eq]
  · simp only [Hybrid.model_step, Hybrid.eval_step, Model.lift_step, Hybrid.get, Mult.model_eq]
  · exact absurd h (by simp)

/-- **Every program over `Arith` with a public trace is private.**  If the
sequence of operations a program issues is the same list `ops` for every
input, its run is its output paired with that list, so the simulator that
outputs `ops` works. -/
theorem arith_private {I α : Type} (c : I → Prog (Arith F).ops .ideal α) (ops : List (Event (Arith F).ops))
    (hview : ∀ i, view (Arith F).eval (c i) = ops) :
    ∃ Sim : PMF (List (Event (Arith F).ops)), ∀ i,
      dist (Arith F).model (c i) = (do let y ← pure (output (Arith F).eval (c i)); let s ← Sim; pure (y, s)) := by
  refine ⟨pure ops, fun i => ?_⟩
  rw [arith_model, dist_lift, hview i]
  simp

-- Correctness is the arithmetic: `output` *is* the evaluation.
example (a b c : F) : output (Arith F).eval (mul3 (fs := Arith F) (D := .ideal) a b c) = a * b * c := rfl
-- `mul3` is straight-line: its view is two multiplication records, whatever the inputs.
example (a b c : F) : view (Arith F).eval (mul3 (fs := Arith F) (D := .ideal) a b c)
    = [⟨⟨1, .mult⟩, ((), ()), (), ()⟩, ⟨⟨1, .mult⟩, ((), ()), (), ()⟩] := rfl
end

end Weft.Examples.Silent
