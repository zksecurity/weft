import Privacy

/-!
# Multiplication from Beaver triples: what "jointly uniform" buys

A multiplication circuit written against three functionalities only:
linear operations, `reveal`, and a `MulTriple` box that hands out `(a, b, a·b)`.
The circuit opens `x − a` and `y − b`.  Its privacy rests on one fact about
the *pair* `(a, b)`: it is uniform on `F²`.  Each of `a` and `b` being
uniform on `F` is not enough, and the last section shows a triple box for
which that is exactly what goes wrong: `a` and `b` each uniform, `c = a·b`
as promised, the circuit still correct, and the two opened values together
publish `x − y`.

In this semantics the joint uniformity is not assumed: a triple is
`(uniform (Fin 2 → F)).map build`, one draw from `F²`, and two triples
from two calls are one draw from `F² × F²` (`uniform_prod`), because each
call is a fresh `bind`.
-/
namespace Glean.Beaver
open Glean Glean.Examples

variable {D : Domain} {σ : Sig}

/-- `x · y` from one triple: open the masked inputs, then only linear operations.
Written once, for any domain and any signature offering the three features. -/
def mulBeaver [Has (Lin D) σ] [Has (Reveal D) σ] [Has (MulTriple D) σ] [Mul D.F] (x y : D.S) : Circ σ D.S := do
  let (a, b, c) ← mulTriple
  let u ← sub x a
  let e ← reveal u              -- e = x − a
  let v ← sub y b
  let d ← reveal v              -- d = y − b
  -- x·y = c + e·b + d·a + e·d
  let t₁ ← smul e b
  let t₂ ← smul d a
  let s ← add c t₁
  let s ← add s t₂
  let ed ← const (e * d)
  add s ed

/-- Two multiplications in sequence, two triples. -/
def mul3Beaver [Has (Lin D) σ] [Has (Reveal D) σ] [Has (MulTriple D) σ] [Mul D.F] (x y z : D.S) : Circ σ D.S := do
  let xy ← mulBeaver x y
  mulBeaver xy z

section
variable (F : Type) [Field F] [Fintype F]
local notation "𝕀" => Domain.ideal F

/-! ## One triple: the pair of masks is one uniform draw from `F²` -/

/-- The semantics of `mulBeaver`: the triple is one uniform draw `v` from `F²`,
the output is `x·y` for every value of `v`, and the two opened values are
`(x − v 0, y − v 1)`. -/
theorem mulBeaver_dist (x y : F) :
    dist (Pre.ideal F) (mulBeaver (D := 𝕀) (σ := Pre 𝕀) x y)
      = (uniform (Fin 2 → F)).bind fun v => pure (x * y, [x - v 0, y - v 1]) := by
  simp [dist, mulBeaver, Pre.ideal, Model.sum, Lin.ideal, Reveal.ideal, MulTriple.ideal, 
    Correlation.sample, MulTriple.corr, sub, reveal, smul, add, const, mulTriple, Circ.op, Has.inj, run,
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.monad_map_eq_map, PMF.map_bind, PMF.pure_map,
    PMF.bind_map, Function.comp_def]
  congr 1
  funext v
  rw [beaver_correct]

/-- Correctness is perfect: the output is `x·y` with certainty. -/
theorem mulBeaver_correct (x y : F) :
    Prod.fst <$> dist (Pre.ideal F) (mulBeaver (D := 𝕀) (σ := Pre 𝕀) x y) = pure (x * y) := by
  rw [mulBeaver_dist]
  simp [PMF.monad_map_eq_map, PMF.monad_pure_eq_pure, PMF.map_bind, PMF.pure_map, PMF.bind_const]

/-- **Hiding.**  `(v 0, v 1) ↦ (x − v 0, y − v 1)` is a bijection of `F²`, so the
opened pair is uniform on `F²` whatever `x, y` are; the simulator draws one. -/
theorem mulBeaver_hiding :
    Hiding (Pre.ideal F) (fun p : F × F => mulBeaver (D := 𝕀) (σ := Pre 𝕀) p.1 p.2) := by
  refine ⟨fun _ => (uniform (F × F)).map fun q => [q.1, q.2], fun p => ?_⟩
  have out := mulBeaver_correct F p.1 p.2
  rw [mulBeaver_dist] at out
  rw [mulBeaver_dist, out, pure_bind]
  simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  let e : (Fin 2 → F) ≃ F × F :=
    (piFinTwoEquiv fun _ => F).trans ((Equiv.subLeft p.1).prodCongr (Equiv.subLeft p.2))
  rw [PMF.bind_map, ← uniform_map_equiv e, PMF.bind_map]
  rfl

/-! ## Two triples: four masks, one uniform draw from `F² × F²`

The two triples come from two calls, i.e. two fresh `bind`s.  The proof
needs the four masks to be *jointly* uniform (the second multiplication's
masked input `x·y − a'` involves the first's output, so the reveals are
not independent of each other in any coordinate-wise sense), and gets it
from `uniform_prod`: two independent draws are one draw from the product. -/

theorem mul3Beaver_dist (x y z : F) :
    dist (Pre.ideal F) (mul3Beaver (D := 𝕀) (σ := Pre 𝕀) x y z)
      = (uniform (Fin 2 → F)).bind fun v => (uniform (Fin 2 → F)).bind fun w =>
          pure (x * y * z, [x - v 0, y - v 1, x * y - w 0, z - w 1]) := by
  rw [mul3Beaver, Circ.bind_eq, dist_bind, mulBeaver_dist]
  simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind]
  congr 1
  funext v
  rw [mulBeaver_dist]
  simp [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind]

/-- Two draws in a row, as one draw from the product, in the shape the proofs use. -/
theorem bind_bind_pure_eq {α β γ : Type} [Fintype α] [Nonempty α] [Fintype β] [Nonempty β] (f : α → β → γ) :
    ((uniform α).bind fun a => (uniform β).bind fun b => (pure (f a b) : PMF γ))
      = (uniform (α × β)).bind fun p => pure (f p.1 p.2) := by
  rw [← uniform_prod]
  simp [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind]

/-- **Hiding, two multiplications.**  The four opened values are the image of the
four masks under a bijection of `F² × F²`, hence uniform on `F⁴`; the
simulator draws four fresh coins. -/
theorem mul3Beaver_hiding :
    Hiding (Pre.ideal F) (fun p : F × F × F => mul3Beaver (D := 𝕀) (σ := Pre 𝕀) p.1 p.2.1 p.2.2) := by
  refine ⟨fun _ => (uniform ((F × F) × (F × F))).map fun q => [q.1.1, q.1.2, q.2.1, q.2.2], fun p => ?_⟩
  rw [mul3Beaver_dist, bind_bind_pure_eq]
  have out : Prod.fst <$> ((uniform ((Fin 2 → F) × (Fin 2 → F))).bind fun q =>
      (pure (p.1 * p.2.1 * p.2.2, [p.1 - q.1 0, p.2.1 - q.1 1, p.1 * p.2.1 - q.2 0, p.2.2 - q.2 1]) :
        PMF (F × List F))) = pure (p.1 * p.2.1 * p.2.2) := by
    simp [PMF.monad_map_eq_map, PMF.monad_pure_eq_pure, PMF.map_bind, PMF.pure_map, PMF.bind_const]
  rw [out, pure_bind]
  simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  let e₁ : (Fin 2 → F) ≃ F × F :=
    (piFinTwoEquiv fun _ => F).trans ((Equiv.subLeft p.1).prodCongr (Equiv.subLeft p.2.1))
  let e₂ : (Fin 2 → F) ≃ F × F :=
    (piFinTwoEquiv fun _ => F).trans ((Equiv.subLeft (p.1 * p.2.1)).prodCongr (Equiv.subLeft p.2.2))
  rw [PMF.bind_map, ← uniform_map_equiv (e₁.prodCongr e₂), PMF.bind_map]
  rfl

/-! ## The counterexample: masks that are each uniform, but not jointly

A "triple" box that draws one coin `a` and hands out `(a, a, a²)`.  Each
component is a correct Beaver triple coordinate-wise: `a` is uniform, `b`
is uniform, `c = a·b`.  `mulBeaver` is still perfectly correct on it.  But
the opened pair `(x − a, y − a)` determines `x − y`, so the circuit is not
hiding: the same output `0` arises from `(0, 0)` and `(1, 0)`, with
disjoint sets of possible views. -/

/-- The degenerate correlation: one coin, used twice. -/
def BadMulTriple.corr : Correlation F (F × F × F) := ⟨1, fun x => (x 0, x 0, x 0 * x 0)⟩
/-- A *wrong model* of the `MulTriple` interface: the only way to state the counterexample. -/
noncomputable def BadMulTriple.ideal : Model (MulTriple 𝕀) F PMF where
  program o := match o with | .get => (BadMulTriple.corr F).sample
  leak _ _ := []
noncomputable def BadPre.ideal : Model (Pre 𝕀) F PMF :=
  ((Lin.ideal F).lift PMF).sum (((Reveal.ideal F).lift PMF).sum (BadMulTriple.ideal F))

omit [Fintype F] in
theorem badBeaver_correct (x y a : F) :
    a * a + (x - a) * a + (y - a) * a + (x - a) * (y - a) = x * y := by ring

/-- Still correct: the output is `x·y`, and the view is `(x − a, y − a)`. -/
theorem mulBeaver_bad_dist (x y : F) :
    dist (BadPre.ideal F) (mulBeaver (D := 𝕀) (σ := Pre 𝕀) x y)
      = (uniform (Fin 1 → F)).bind fun v => pure (x * y, [x - v 0, y - v 0]) := by
  simp [dist, mulBeaver, BadPre.ideal, BadMulTriple.ideal, Model.sum, Lin.ideal, Reveal.ideal, 
    Correlation.sample, BadMulTriple.corr, sub, reveal, smul, add, const, mulTriple, Circ.op, Has.inj, run,
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.monad_map_eq_map, PMF.map_bind, PMF.pure_map,
    PMF.bind_map, Function.comp_def]
  congr 1
  funext v
  rw [badBeaver_correct]

/-- **Not hiding.**  Any simulator must, on output `0`, produce a view that is
possible both for `(0, 0)` (views `[−a, −a]`) and for `(1, 0)` (views
`[1 − a, −a]`); no list is both. -/
theorem mulBeaver_bad_not_hiding :
    ¬ Hiding (BadPre.ideal F) (fun p : F × F => mulBeaver (D := 𝕀) (σ := Pre 𝕀) p.1 p.2) := by
  rintro ⟨Sim, h⟩
  -- both inputs have output 0 with certainty, so both real distributions equal `Sim 0` tagged with 0
  have out : ∀ p : F × F, Prod.fst <$> dist (BadPre.ideal F) (mulBeaver (D := 𝕀) (σ := Pre 𝕀) p.1 p.2)
      = pure (p.1 * p.2) := by
    intro p
    rw [mulBeaver_bad_dist]
    simp [PMF.monad_map_eq_map, PMF.monad_pure_eq_pure, PMF.map_bind, PMF.pure_map, PMF.bind_const]
  have h₀ := h (0, 0)
  have h₁ := h (1, 0)
  rw [out, pure_bind] at h₀ h₁
  simp only [mul_zero, zero_mul, one_mul] at h₀ h₁
  have same := h₀.trans h₁.symm
  -- the view `[1, 0]` is possible for `(1, 0)` (mask `a = 0`) ...
  have mem₁ : ((0 : F), [(1 : F), 0]) ∈ (dist (BadPre.ideal F) (mulBeaver (D := 𝕀) (σ := Pre 𝕀) 1 0)).support := by
    rw [mulBeaver_bad_dist]
    simp only [PMF.monad_pure_eq_pure, PMF.support_bind, PMF.support_pure, Set.mem_iUnion, Set.mem_singleton_iff]
    exact ⟨fun _ => 0, by simp, by simp⟩
  -- ... hence, by `same`, for `(0, 0)`: but there every view is `[−a, −a]`
  rw [← same, mulBeaver_bad_dist] at mem₁
  simp [PMF.monad_pure_eq_pure, PMF.support_bind, PMF.support_pure] at mem₁
  obtain ⟨a, h1, h2⟩ := mem₁
  rw [h2, neg_zero] at h1
  exact zero_ne_one h1
end

end Glean.Beaver
