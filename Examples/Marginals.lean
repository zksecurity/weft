import Weft

/-!
# Response and leakage marginals

The accessors project the existing joint step; they do not override it.
-/
namespace Weft.Examples.Marginals

example {ι : Interface} {D : Domain} {m : Type → Type} [Functor m]
    (M : Model ι D m) (r : Req ι D) :
    M.response r = Prod.fst <$> M.step r := rfl

example {ι : Interface} {D : Domain} {m : Type → Type} [Functor m]
    (M : Model ι D m) (r : Req ι D) :
    M.leakage r = Prod.snd <$> M.step r := rfl

example (F : Functionality) (r : Req F.ops .ideal) :
    F.response r = Prod.fst <$> F.model.step r := rfl

example (F : Functionality) (r : Req F.ops .ideal) :
    F.leakage r = Prod.snd <$> F.model.step r := rfl

private abbrev bitOps : Interface :=
  ⟨Unit, fun _ => [], fun _ => .share Bool, fun _ => Bool⟩

private def fixedModel : Model bitOps .ideal Id :=
  ⟨fun _ => (true, false)⟩

-- Distinct values ensure the two projections cannot be swapped.
example : fixedModel.response ⟨(), ()⟩ = true := rfl
example : fixedModel.leakage ⟨(), ()⟩ = false := rfl

private noncomputable def correlatedModel : Model bitOps .ideal PMF :=
  ⟨fun _ => (uniform Bool).map fun b => (b, b)⟩

-- Both marginals are uniform, but the joint step preserves their correlation.
example : correlatedModel.response ⟨(), ()⟩ = uniform Bool := by
  change ((uniform Bool).map (fun b => (b, b))).map Prod.fst = _
  rw [PMF.map_comp]
  exact PMF.map_id _

example : correlatedModel.leakage ⟨(), ()⟩ = uniform Bool := by
  change ((uniform Bool).map (fun b => (b, b))).map Prod.snd = _
  rw [PMF.map_comp]
  exact PMF.map_id _

example : ∀ p ∈ (correlatedModel.step ⟨(), ()⟩).support, p.1 = p.2 := by
  intro p hp
  change p ∈ ((uniform Bool).map fun b => (b, b)).support at hp
  rw [PMF.support_map] at hp
  obtain ⟨b, _, h⟩ := hp
  cases h
  rfl

-- The renamed accessors replace the old names rather than retaining aliases.
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for name in [`Weft.Model.program, `Weft.Functionality.program] do
    if env.contains name then
      throwError "legacy projection still exists: {name}"

end Weft.Examples.Marginals
