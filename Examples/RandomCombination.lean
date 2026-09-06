import Weft
import Examples.Basic

/-!
# A random disclosure that is not a function of the response

A random linear combination with a public coin: `Σ rⁱ·xᵢ` for a fresh
public `r`.  Its honest specification returns the share of the combination
and *discloses* `r`, which no honest party receives; the disclosure is not
a function of the response (on all-zero inputs the response is `0` for
every `r`).  A model with a deterministic `leak (request, response)`
cannot say this; one joint `step` can (report, Issue 5).  The old claim
that this program "is hiding" was false: the response and the coin are
correlated, and a caller that later opens the result learns both.
-/
namespace Weft.Examples.RandCombination
open Weft.Examples.Basic

/-! ### The functionality: two operands, a share response, a disclosed field element -/

namespace RC
inductive Op where | rc
abbrev ops (F : Type) : Interface where
  Op := Op
  dom _ := [.share F, .share F]
  cod _ := .share F
  leak _ := F
/-- The joint step: draw `r`, return `x₀ + r·x₁`, disclose `r`. -/
noncomputable def model (F : Type) [Add F] [Mul F] [Fintype F] [Inhabited F] : Model (ops F) .ideal PMF :=
  ⟨fun r => (uniform F).map fun c => (r.args.1 + c * r.args.2.1, c)⟩
/-- With the coin fixed to the dummy. -/
def eval (F : Type) [Add F] [Mul F] [Inhabited F] : Model (ops F) .ideal Id :=
  ⟨fun r => pure (r.args.1 + default * r.args.2.1, default)⟩
end RC

/-- The random-combination functionality of two shares. -/
abbrev RandComb (F : Type) [Add F] [Mul F] [Fintype F] [Inhabited F] : Functionality :=
  ⟨RC.ops F, RC.eval F, (· = RC.model F), Functionality.unique_eq _⟩

@[simp, weft] theorem RandComb.model_eq (F : Type) [Add F] [Mul F] [Fintype F] [Inhabited F] :
    (RandComb F).model = RC.model F := Functionality.model_eq rfl

section
variable (F : Type) [Field F] [Fintype F] [Inhabited F]

/-- The program: a public coin, then linear operations. -/
def randComb2 {fs : Hybrid} {D : Domain} [Has (Lin F) fs] [Has (PubCoin F) fs] (x₀ x₁ : D.share F) :
    Prog fs.ops D (D.share F) := do
  let r ← coin F
  let t ← smul r x₁
  add x₀ t

/-- The hybrid with a public coin. -/
abbrev CoinHyb : Hybrid := [Lin F, PubCoin F]

/-- **The program realises the functionality.**  The event carries the
disclosed coin, and the simulator replays it: the coin record, the scalar
multiplication by it, the addition. -/
program randComb2Real : Realization (RandComb F) (CoinHyb F) where
  impl D r := randComb2 F r.args.1 r.args.2.1
  Sim e := pure [⟨⟨1, .coin⟩, (), e.leak, ()⟩, ⟨⟨0, .smul⟩, (e.leak, (), ()), (), ()⟩, ⟨⟨0, .add⟩, ((), (), ()), (), ()⟩]
  real r _ := by
    obtain ⟨⟨⟩, x₀, x₁, ⟨⟩⟩ := r
    simp only [randComb2, coin, smul, add, weft, RC.model]
    rfl
end

end Weft.Examples.RandCombination
