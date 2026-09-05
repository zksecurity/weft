import Weft.Realization

/-!
# Statistical realisations

A statistical realisation keeps correctness perfect (the output marginal
is exactly the functionality's) and allows the real and the simulated
joint (output, view) distributions to differ by at most `ε` in total
variation, per operation.  The bound is on the joint, not on the view
alone: over `𝔽₂`, `b ← rand; reveal (x + b); pure b` has a uniform view
for every `x`, so an independent-coin simulator is at distance 0 on the
view while a later opening of `b` reveals `x`.

Composition rests on one kernel lemma, `statDist_bind_le`: the distance
of two binds is at most the distance of the first draws plus the expected
distance of the continuations.  The caller's budget is then the sum, over
its ideal execution, of the per-request errors.
-/
namespace Weft

/-- Truncated subtraction is subadditive under a sum. -/
theorem ENNReal.tsum_tsub_le {A : Type} (f g : A → ENNReal) : (∑' a, f a) - (∑' a, g a) ≤ ∑' a, (f a - g a) := by
  rw [tsub_le_iff_right, ← ENNReal.tsum_add]
  exact ENNReal.tsum_le_tsum fun a => le_tsub_add

/-- **The kernel lemma.**  Total variation of two binds. -/
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

/-- Data processing: a common postprocessing does not increase the distance. -/
theorem PMF.statDist_map_le {A B : Type} (p q : PMF A) (h : A → B) :
    PMF.statDist (p.map h) (q.map h) ≤ PMF.statDist p q := by
  have := PMF.statDist_bind_le p q (fun a => PMF.pure (h a)) (fun a => PMF.pure (h a))
  simpa [PMF.map, PMF.statDist_self] using this

/-- **A statistical realisation**: exact output marginal, joint within `ε` per operation. -/
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

/-- The caller's budget: the sum, over the ideal execution, of the errors
of the requests it issues.  `min 1` of it is automatic, since total
variation is at most one. -/
noncomputable def budget {ι : Interface} (M : Model ι .ideal PMF) (ε : ι.Op → ENNReal) {α : Type} :
    Prog ι .ideal α → ENNReal
  | .pure _ => 0
  | .call r k => ε r.op + ∑' z, M.step r z * budget M ε (k z.1)

end Weft
