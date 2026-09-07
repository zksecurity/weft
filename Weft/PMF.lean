import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Probability lemmas

Uniform sampling under bijections, joint uniformity of independent draws,
congruence on distribution supports, and total variation distance.
-/
namespace Weft

/-- Uniform coins over a finite alphabet: Mathlib's `PMF.uniformOfFintype`. -/
notation "uniform" => PMF.uniformOfFintype

theorem PMF.monad_bind_eq_bind {α β : Type} (p : PMF α) (f : α → PMF β) : p >>= f = p.bind f := rfl
theorem PMF.monad_pure_eq_pure {α : Type} (a : α) : (pure a : PMF α) = PMF.pure a := rfl
theorem PMF.monad_map_eq_map {α β : Type} (f : α → β) (p : PMF α) : f <$> p = p.map f := rfl

/-- Bijections preserve the uniform distribution.
For a fixed secret, a bijection of a fresh uniform mask remains uniform;
hence its distribution is independent of the secret. -/
theorem uniform_map_equiv {α β : Type} [Fintype α] [Nonempty α] [Fintype β] [Nonempty β] (e : α ≃ β) :
    (uniform α).map e = uniform β := by
  ext b
  rw [PMF.map_apply, PMF.uniformOfFintype_apply, tsum_eq_single (e.symm b)]
  · simp [Fintype.card_congr e]
  · intro a ha
    have : b ≠ e a := fun h => ha (by rw [h, Equiv.symm_apply_apply])
    simp [this]

section Joint
variable {α β : Type} [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]

/-- Independent uniform draws give the uniform distribution on the product. -/
theorem uniform_prod :
    (do let a ← uniform α; let b ← uniform β; pure (a, b)) = uniform (α × β) := by
  ext ⟨a, b⟩
  simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_apply, PMF.uniformOfFintype_apply,
    PMF.pure_apply, Prod.mk.injEq]
  rw [tsum_eq_single a, tsum_eq_single b]
  · simp [Fintype.card_prod, ENNReal.mul_inv]
  · intro b' hb; simp [Ne.symm hb]
  · intro a' ha; simp [Ne.symm ha]

/-- Combine two independent uniform draws before applying `f`. -/
theorem bind_bind_pure_eq {γ : Type} (f : α → β → γ) :
    ((uniform α).bind fun a => (uniform β).bind fun b => (pure (f a b) : PMF γ))
      = (uniform (α × β)).bind fun p => pure (f p.1 p.2) := by
  rw [← uniform_prod]
  simp [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind]

/-- `n` fresh draws in sequence. -/
noncomputable def seqUniform (F : Type) [Fintype F] [Nonempty F] : (n : Nat) → PMF (Fin n → F)
  | 0 => pure fun i => i.elim0
  | n + 1 => do
    let x ← uniform F
    let xs ← seqUniform F n
    pure (Fin.cons x xs)

/-- Sequential independent draws are jointly uniform on `Fⁿ`. -/
theorem seqUniform_eq_uniform (F : Type) [Fintype F] [Nonempty F] :
    ∀ n, seqUniform F n = uniform (Fin n → F)
  | 0 => by
    ext v
    simp only [seqUniform, PMF.monad_pure_eq_pure, PMF.pure_apply, PMF.uniformOfFintype_apply]
    have : v = fun i => i.elim0 := funext fun i => i.elim0
    simp [this]
  | n + 1 => by
    have h : seqUniform F (n + 1) =
        ((do let a ← uniform F; let b ← uniform (Fin n → F); pure (a, b)) :
          PMF (F × (Fin n → F))).map fun p => Fin.cons p.1 p.2 := by
      simp only [seqUniform, seqUniform_eq_uniform F n, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
        PMF.map_bind, PMF.pure_map]
    rw [h, uniform_prod]
    exact uniform_map_equiv (Fin.consEquiv fun _ => F)
end Joint

/-! ### Congruence on the support -/

/-- Two continuations that agree on the support of `p` give the same bind. -/
theorem PMF.bind_congr_support {α β : Type} {p : PMF α} {f g : α → PMF β} (h : ∀ a ∈ p.support, f a = g a) :
    p.bind f = p.bind g := by
  ext b
  simp only [PMF.bind_apply]
  refine tsum_congr fun a => ?_
  by_cases ha : a ∈ p.support
  · rw [h a ha]
  · simp [(PMF.apply_eq_zero_iff p a).2 ha]

/-- Two functions that agree on the support of `p` give the same image. -/
theorem PMF.map_congr_support {α β : Type} {p : PMF α} {f g : α → β} (h : ∀ a ∈ p.support, f a = g a) :
    p.map f = p.map g := by
  ext b
  simp only [PMF.map_apply]
  refine tsum_congr fun a => ?_
  by_cases ha : a ∈ p.support
  · rw [h a ha]
  · simp [(PMF.apply_eq_zero_iff p a).2 ha]

/-! ### Total variation -/

/-- Total variation distance between two discrete distributions. -/
noncomputable def PMF.statDist {β : Type} (p q : PMF β) : ENNReal := ∑' b, (p b - q b)

theorem PMF.statDist_self {β : Type} (p : PMF β) : PMF.statDist p p = 0 := by
  simp [PMF.statDist]

theorem PMF.statDist_eq_zero_of_eq {β : Type} {p q : PMF β} (h : p = q) : PMF.statDist p q = 0 := by
  subst h; exact PMF.statDist_self p

/-- Zero distance is equality (both sides are probability distributions). -/
theorem PMF.eq_of_statDist_eq_zero {β : Type} {p q : PMF β} (h : PMF.statDist p q = 0) : p = q := by
  have le : ∀ b, p b ≤ q b := fun b =>
    tsub_eq_zero_iff_le.1 ((ENNReal.tsum_eq_zero.1 h) b)
  ext b
  by_contra hb
  have lt : p b < q b := lt_of_le_of_ne (le b) hb
  have := ENNReal.tsum_lt_tsum (i := b) (by rw [p.tsum_coe]; exact ENNReal.one_ne_top) le lt
  rw [p.tsum_coe, q.tsum_coe] at this
  exact lt_irrefl _ this

/-- Total variation is at most one. -/
theorem PMF.statDist_le_one {β : Type} (p q : PMF β) : PMF.statDist p q ≤ 1 := by
  calc PMF.statDist p q = ∑' b, (p b - q b) := rfl
    _ ≤ ∑' b, p b := ENNReal.tsum_le_tsum fun b => tsub_le_self
    _ = 1 := p.tsum_coe

end Weft
