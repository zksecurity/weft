import Weft.Realization

/-!
# Statistical realisations

A statistical realisation has the exact ideal output marginal,
with total variation at most `ε` between the real and simulated joint distributions.

The joint bound matters even when the view alone is uniform.
Over `𝔽₂`, consider `b ← rand; reveal (x + b); pure b`.
The view is uniform for every `x`,
but opening the returned `b` reveals `x`.

`statDist_bind_le` adds two terms:
the initial sampling distance and the expected continuation distance.
`budget` sums per-request errors along the ideal execution;
the composition bound using this budget remains to be proved.
-/
namespace Weft

/-- Truncated subtraction is subadditive under a sum. -/
theorem ENNReal.tsum_tsub_le {A : Type} (f g : A → ENNReal) : (∑' a, f a) - (∑' a, g a) ≤ ∑' a, (f a - g a) := by
  rw [tsub_le_iff_right, ← ENNReal.tsum_add]
  exact ENNReal.tsum_le_tsum fun a => le_tsub_add

/-- Bound bind distance by initial distance plus expected continuation distance. -/
theorem PMF.statDist_bind_le {A B : Type} (p q : PMF A) (f g : A → PMF B) :
    PMF.statDist (p.bind f) (q.bind g) ≤ PMF.statDist p q + ∑' a, q a * PMF.statDist (f a) (g a) := by
  have point : ∀ a b, p a * f a b - q a * g a b ≤ (p a - q a) * f a b + q a * (f a b - g a b) := by
    intro a b
    rw [tsub_le_iff_right]
    calc p a * f a b ≤ ((p a - q a) + q a) * f a b := by gcongr; exact le_tsub_add
      _ = (p a - q a) * f a b + q a * f a b := by rw [add_mul]
      _ ≤ (p a - q a) * f a b + q a * ((f a b - g a b) + g a b) := by gcongr; exact le_tsub_add
      _ = (p a - q a) * f a b + q a * (f a b - g a b) + q a * g a b := by rw [mul_add, add_assoc]
  calc PMF.statDist (p.bind f) (q.bind g)
      = ∑' b, ((∑' a, p a * f a b) - ∑' a, q a * g a b) := by simp [PMF.statDist, PMF.bind_apply]
    _ ≤ ∑' b, ∑' a, (p a * f a b - q a * g a b) := ENNReal.tsum_le_tsum fun b => ENNReal.tsum_tsub_le _ _
    _ ≤ ∑' b, ∑' a, ((p a - q a) * f a b + q a * (f a b - g a b)) :=
        ENNReal.tsum_le_tsum fun b => ENNReal.tsum_le_tsum fun a => point a b
    _ = ∑' a, ∑' b, ((p a - q a) * f a b + q a * (f a b - g a b)) := ENNReal.tsum_comm
    _ = ∑' a, ((p a - q a) * ∑' b, f a b + q a * ∑' b, (f a b - g a b)) := by
        congr 1; funext a; rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
    _ = ∑' a, ((p a - q a) + q a * PMF.statDist (f a) (g a)) := by
        congr 1; funext a; rw [(f a).tsum_coe, mul_one]; rfl
    _ = PMF.statDist p q + ∑' a, q a * PMF.statDist (f a) (g a) := by
        rw [ENNReal.tsum_add]; rfl

/-- Applying the same function to both distributions cannot increase total variation. -/
theorem PMF.statDist_map_le {A B : Type} (p q : PMF A) (h : A → B) :
    PMF.statDist (p.map h) (q.map h) ≤ PMF.statDist p q := by
  have := PMF.statDist_bind_le p q (fun a => PMF.pure (h a)) (fun a => PMF.pure (h a))
  simpa [PMF.map, PMF.statDist_self, Function.comp_def] using this

/-- Exact output marginal and joint simulation error bounded by `ε` per operation. -/
structure RealizationStat (F : Functionality) (fs : Hybrid) where
  impl : (D : Domain) → (r : Req F.ops D) → Prog fs.ops D (Resp F.ops D r.op)
  Pre : Req F.ops .ideal → Prop := fun _ => True
  Sim : Event F.ops → PMF (List (Event fs.ops))
  ε : F.ops.Op → ENNReal
  output : ∀ r, Pre r → Prod.fst <$> dist fs.model (impl .ideal r) = F.program r
  close : ∀ r, Pre r → PMF.statDist (dist fs.model (impl .ideal r)) (do
    let (y, d) ← F.model.step r
    let s ← Sim ⟨r.op, r.args.blank, (F.ops.cod r.op).blank y, d⟩
    pure (y, s)) ≤ ε r.op

/-- A perfect realisation is a statistical one with `ε = 0`. -/
noncomputable def Realization.toStat {F : Functionality} {fs : Hybrid} (f : Realization F fs) :
    RealizationStat F fs where
  impl := f.impl
  Pre := f.Pre
  Sim := f.Sim
  ε _ := 0
  output r hr := by
    rw [f.real r hr]
    simp [PMF.monad_bind_eq_bind, PMF.monad_map_eq_map, PMF.monad_pure_eq_pure, PMF.map_bind, PMF.pure_map,
      PMF.bind_const, Model.program]
    rfl
  close r hr := le_of_eq (PMF.statDist_eq_zero_of_eq (f.real r hr))

/-- Expected sum of per-request errors along the ideal execution. -/
noncomputable def budget {ι : Interface} (M : Model ι .ideal PMF) (ε : ι.Op → ENNReal) {α : Type} :
    Prog ι .ideal α → ENNReal
  | .pure _ => 0
  | .call r k => ε r.op + ∑' z, M.step r z * budget M ε (k z.1)
  | .look c k => budget M ε (k c)

end Weft
