import Weft
import Examples.Basic

/-!
# Joint sampling of response and disclosure

The functionality returns a share of `x₀ + r·x₁` and discloses uniform `r`.
The disclosure cannot be recovered from the request and response:
when both inputs are zero, every coin gives the same response.
A joint model step records the correlation.

The implementation draws a public coin and performs linear operations.
Its simulator uses the disclosed coin to reproduce the event list.
-/
namespace Weft.Examples.RandCombination
open Weft.Examples.Basic

/-! ### Random-combination functionality -/

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
/-- Evaluate with the coin fixed to `default`. -/
def eval (F : Type) [Add F] [Mul F] [Inhabited F] : Model (ops F) .ideal Id :=
  ⟨fun r => pure (r.args.1 + default * r.args.2.1, default)⟩
end RC

/-- Return a shared random combination and disclose its coefficient. -/
abbrev RandComb (F : Type) [Add F] [Mul F] [Fintype F] [Inhabited F] : Functionality :=
  ⟨RC.ops F, RC.eval F, (· = RC.model F), Functionality.unique_eq _⟩

@[simp, weft] theorem RandComb.model_eq (F : Type) [Add F] [Mul F] [Fintype F] [Inhabited F] :
    (RandComb F).model = RC.model F := Functionality.model_eq rfl

section
variable (F : Type) [Field F] [Fintype F] [Inhabited F]

/-- Compute `x₀ + r·x₁` using a public coin. -/
def randComb2 {fs : Hybrid} {D : Domain} [Has (Lin F) fs] [Has (PubCoin F) fs] (x₀ x₁ : D.share F) :
    Prog fs.ops D (D.share F) := do
  let r ← coin F
  let t ← smul r x₁
  add x₀ t

/-- Linear operations and public coins. -/
abbrev CoinHyb : Hybrid := [Lin F, PubCoin F]

/-- Simulate the coin, scalar multiplication and addition events using the disclosed coefficient. -/
program randComb2Real : Realization (RandComb F) (CoinHyb F) where
  impl D r := randComb2 F r.args.1 r.args.2.1
  Sim e := pure [⟨⟨1, .coin⟩, (), e.leak, ()⟩, ⟨⟨0, .smul⟩, (e.leak, (), ()), (), ()⟩, ⟨⟨0, .add⟩, ((), (), ()), (), ()⟩]
  real r _ := by
    obtain ⟨⟨⟩, x₀, x₁, ⟨⟩⟩ := r
    simp only [randComb2, coin, smul, add, weft, RC.model]
    rfl
end

end Weft.Examples.RandCombination
