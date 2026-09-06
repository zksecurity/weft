import Weft

/-!
# What the `program` command rejects

A certificate's implementation must be a computable, domain-generic
program: that is what makes "the simulator sees only the event" mean what
it says, because such a program can do nothing with a share except pass it
to an operation.  Lean rejects share comparison in a computable `def`
already; the command closes the remaining gaps.
-/
namespace Weft.Examples.Checked

section
variable (F : Type) [Field F] [DecidableEq F]

/-- The identity functionality on a share. -/
abbrev Keep : Functionality :=
  .ofEval ⟨Unit, fun _ => [.share F], fun _ => .share F, fun _ => Unit⟩
    ⟨fun r => pure (r.args.1, ())⟩

/-- A program that branches on a share, at the ideal domain, where a share
is its value.  Lean accepts the definition, since `F` has decidable
equality; `program` does not accept it as an implementation, because it is
not generic in the domain (its type fixes `Domain.ideal`). -/
def peekIdeal {fs : Hybrid} [Has (Lin F) fs] (x : F) : Prog fs.ops .ideal F :=
  if x = 0 then do let _ ← const (0 : F); pure x else pure x

-- A domain-generic version needs decidable equality on `D.share F`, which no
-- program has; supplying it classically makes the definition noncomputable.
noncomputable def peek {fs : Hybrid} {D : Domain} [Has (Lin F) fs] (x : D.share F) : Prog fs.ops D (D.share F) := by
  classical
  exact if x = x then pure x else do let _ ← const (0 : D.clear F); pure x

-- `program` refuses the classical implementation.
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

-- ...and a certificate whose parameters hand it a way to inspect shares.
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

-- The honest implementation passes.
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
