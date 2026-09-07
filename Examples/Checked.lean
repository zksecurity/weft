import Weft

/-!
# Implementation-checker tests

`program` rejects a noncomputable implementation and a parameter that can inspect shares.
A direct identity implementation passes.
The doc comments attached to `#guard_msgs` specify the expected diagnostics.
-/
namespace Weft.Examples.Checked

section
variable (F : Type) [Field F] [DecidableEq F]

/-- The identity functionality on a share. -/
abbrev Keep : Functionality :=
  .ofEval ⟨Unit, fun _ => [.share F], fun _ => .share F, fun _ => Unit⟩
    ⟨fun r => pure (r.args.1, ())⟩

/-- Inspect a share in the ideal domain, where shares are plain values.
The fixed domain prevents this definition from serving as a generic implementation. -/
def peekIdeal {fs : Hybrid} [Has (Lin F) fs] (x : F) : Prog fs.ops .ideal F :=
  if x = 0 then do let _ ← const (0 : F); pure x else pure x

-- Comparing generic shares requires `DecidableEq (D.share F)`.
-- Obtaining this instance classically makes the definition noncomputable.
noncomputable def peek {fs : Hybrid} {D : Domain} [Has (Lin F) fs] (x : D.share F) : Prog fs.ops D (D.share F) := by
  classical
  exact if x = x then pure x else do let _ ← const (0 : D.clear F); pure x

-- Reject the noncomputable implementation.
/--
error: program: the implementation uses `Weft.Examples.Checked.peek`, which is noncomputable
---
warning: declaration uses `sorry`
-/
#guard_msgs in
program peekReal : Realization (Keep F) (Std F) where
  impl D r := peek F r.args.1
  Sim _ := pure []
  real := sorry

-- Reject a parameter that supplies share inspection.
/--
error: program: parameter `peekAt` mentions a domain; its type is `(D : Domain) → D.share F → Bool`.
A certificate's implementation must be generic in the domain and may not receive anything that inspects shares.
---
warning: declaration uses `sorry`
-/
#guard_msgs in
program peekParam (peekAt : (D : Domain) → D.share F → Bool) : Realization (Keep F) (Std F) where
  impl D r := if peekAt D r.args.1 then pure r.args.1 else pure r.args.1
  Sim _ := pure []
  real := sorry

-- Accept the direct identity implementation.
/-- info: program: `Weft.Examples.Checked.keepReal` certified; its implementation is a computable, domain-generic program. -/
#guard_msgs in
program keepReal : Realization (Keep F) (Std F) where
  impl D r := pure r.args.1
  Sim _ := pure []
  real r _ := by
    obtain ⟨⟨⟩, x, ⟨⟩⟩ := r
    simp [weft]
end

end Weft.Examples.Checked
