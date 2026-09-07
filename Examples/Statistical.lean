import Weft
import Examples.Beaver

/-!
# Statistical realisation examples

Convert Beaver multiplication to a zero-error statistical realisation,
apply the bind-distance bound, and unfold a two-request error budget.
-/
namespace Weft.Examples.Statistical
open Weft.Examples.Beaver

section
variable (F : Type) [Field F] [Fintype F] [Inhabited F]

/-- Beaver multiplication, as a statistical realisation with error zero. -/
noncomputable def beaverStat : RealizationStat (Mult F) (Pre F) := (beaverMult F).toStat

example (o : (Mult F).ops.Op) : (beaverStat F).ε o = 0 := rfl

/-- A common continuation does not increase the initial sampling distance. -/
example (p q : PMF F) (k : F → PMF (F × F)) :
    PMF.statDist (p.bind k) (q.bind k) ≤ PMF.statDist p q := by
  have := PMF.statDist_bind_le p q k k
  simpa [PMF.statDist_self] using this

/-- A two-request caller's budget is the first error plus the expected second. -/
example (M : Model (Std F).ops .ideal PMF) (ε : (Std F).ops.Op → ENNReal) (r : Req (Std F).ops .ideal)
    (k : Resp (Std F).ops .ideal r.op → Req (Std F).ops .ideal) :
    budget M ε (.call r fun y => .call (k y) fun _ => .pure ()) = ε r.op + ∑' z, M.step r z * ε (k z.1).op := by
  simp [budget]
end

end Weft.Examples.Statistical
