import Weft

/-!
# Beaver multiplication

Given a triple `(a, b, a·b)`,
open `e = x − a` and `d = y − b`,
then compute the product using linear operations:
`x·y = a·b + e·b + d·a + e·d`.

With precomputed triples,
the protocol uses two independent openings in one round.
For independent uniform `a` and `b`,
the bijection `(a, b) ↦ (x − a, y − b)` makes the openings jointly uniform.
Hence their distribution is independent of the inputs.

The final example uses correlated masks `(a, a)`.
The product remains correct, but the openings reveal `x − y`.
Uniform marginals alone do not suffice.
-/
namespace Weft.Examples.Beaver

section Programs
variable {F : Type} [Add F] [Mul F] [Sub F] [Fintype F] [Inhabited F] {fs : Hybrid} {D : Domain}

/-- Beaver multiplication parameterised by its triple source.
Correctness requires `c = a·b`;
privacy additionally requires independent uniform masks. -/
def mulBeaverFrom [Has (Lin F) fs] [Has (Reveal F) fs] (triple : Prog fs.ops D (D.share F × D.share F × D.share F))
    (x y : D.share F) : Prog fs.ops D (D.share F) := do
  let (a, b, c) ← triple
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

/-- Use the independent masks supplied by `MulTriple`. -/
def mulBeaver [Has (Lin F) fs] [Has (Reveal F) fs] [Has (MulTriple F) fs] (x y : D.share F) : Prog fs.ops D (D.share F) :=
  mulBeaverFrom (mulTriple F) x y

/-- Multiply three shares using two triples. -/
def mul3Beaver [Has (Lin F) fs] [Has (Reveal F) fs] [Has (MulTriple F) fs] (x y z : D.share F) :
    Prog fs.ops D (D.share F) := do
  let xy ← mulBeaver x y
  mulBeaver xy z
end Programs

/-! ## Evaluation and costs -/

section MPCs
variable (F : Type) [Add F] [Mul F] [Sub F] [Fintype F] [Inhabited F]
/-- Precomputed triples are free; each opening costs one round and one unit. -/
abbrev preMPC : MPC := [(Lin F).priced ⟨0, 0⟩, (Reveal F).priced ⟨1, 1⟩, (MulTriple F).priced ⟨0, 0⟩]
/-- Charge two rounds and three units for online triple generation. -/
abbrev preOnline : MPC := [(Lin F).priced ⟨0, 0⟩, (Reveal F).priced ⟨1, 1⟩, (MulTriple F).priced ⟨2, 3⟩]
end MPCs

section Evaluation
variable (F : Type) [Add F] [Mul F] [Sub F] [Fintype F] [Inhabited F]

/-- The view of one Beaver multiplication, as a function of the two opened values. -/
def beaverView (q : F × F) : List (Event (Pre F).ops) :=
  [⟨Pre.triple F, (), ((), (), ()), ()⟩, ⟨Pre.lin F .sub, ((), (), ()), (), ()⟩, ⟨Pre.reveal F, ((), ()), q.1, ()⟩, ⟨Pre.lin F .sub, ((), (), ()), (), ()⟩,
   ⟨Pre.reveal F, ((), ()), q.2, ()⟩, ⟨Pre.lin F .smul, (q.1, (), ()), (), ()⟩, ⟨Pre.lin F .smul, (q.2, (), ()), (), ()⟩,
   ⟨Pre.lin F .add, ((), (), ()), (), ()⟩, ⟨Pre.lin F .add, ((), (), ()), (), ()⟩, ⟨Pre.lin F .const, (q.1 * q.2, ()), (), ()⟩,
   ⟨Pre.lin F .add, ((), (), ()), (), ()⟩]

-- `mulBeaver_dist` samples the two masked inputs,
-- then applies `beaverView` to obtain the view.

-- Two openings at one communication unit each.
example : commOn (preMPC (Fin 7)).timed
    (mulBeaver (F := Fin 7) (fs := (preMPC (Fin 7)).hybrid) (D := .timed) ⟪3⟫ ⟪4⟫) = 2 := by decide +kernel
end Evaluation

section Closed
/-! Use `decide +kernel` for the closed `Fin 7` instances.
It avoids the elaborator's reduction overhead when evaluating these programs. -/

-- Online generation adds the triple's three communication units.
example : commOn (preOnline (Fin 7)).timed
    (mulBeaver (F := Fin 7) (fs := (preOnline (Fin 7)).hybrid) (D := .timed) ⟪3⟫ ⟪4⟫) = 5 := by decide +kernel
-- Independent openings take one round after the triple is available.
example : delayOn (preMPC (Fin 7)).timed
    (mulBeaver (F := Fin 7) (fs := (preMPC (Fin 7)).hybrid) (D := .timed) ⟪3⟫ ⟪4⟫) = 1 := by decide +kernel
example : delayOn (preOnline (Fin 7)).timed
    (mulBeaver (F := Fin 7) (fs := (preOnline (Fin 7)).hybrid) (D := .timed) ⟪3⟫ ⟪4⟫) = 3 := by decide +kernel
-- Two chained multiplications: two rounds, four openings.
example : delayOn (preMPC (Fin 7)).timed
    (mul3Beaver (F := Fin 7) (fs := (preMPC (Fin 7)).hybrid) (D := .timed) ⟪3⟫ ⟪4⟫ ⟪5⟫) = 2 := by
  decide +kernel
example : commOn (preMPC (Fin 7)).timed
    (mul3Beaver (F := Fin 7) (fs := (preMPC (Fin 7)).hybrid) (D := .timed) ⟪3⟫ ⟪4⟫ ⟪5⟫) = 4 := by
  decide +kernel
end Closed

/-! ## Correctness and privacy -/

section Privacy
variable (F : Type) [Field F] [Fintype F] [Inhabited F]

omit [Fintype F] [Inhabited F] in
theorem beaver_correct (x y : F) (v : Fin 2 → F) :
    v 0 * v 1 + (x - v 0) * v 1 + (y - v 1) * v 0 + (x - v 0) * (y - v 1) = x * y := by ring

/-- The output is `x·y` for every mask pair.
The view is determined by the openings `(x − v 0, y − v 1)`. -/
theorem mulBeaver_dist (x y : F) :
    dist (Pre F).model (mulBeaver (fs := Pre F) (D := .ideal) x y)
      = (uniform (Fin 2 → F)).bind fun v => pure (x * y, beaverView F (x - v 0, y - v 1)) := by
  simp only [mulBeaver, mulBeaverFrom, beaverView, mulTriple, sub, reveal, smul, add, const, weft]
  congr 1
  funext v
  rw [beaver_correct]
  rfl

/-- The output distribution is a point mass at `x·y`. -/
theorem mulBeaver_correct (x y : F) :
    Prod.fst <$> dist (Pre F).model (mulBeaver (fs := Pre F) (D := .ideal) x y) = pure (x * y) := by
  rw [mulBeaver_dist]
  simp [PMF.monad_map_eq_map, PMF.monad_pure_eq_pure, PMF.map_bind, PMF.pure_map, PMF.bind_const]

/-- The masks: `(a, b) ↦ (x − a, y − b)` is a bijection of `F²`. -/
def maskEquiv (x y : F) : (Fin 2 → F) ≃ F × F :=
  (piFinTwoEquiv fun _ => F).trans ((Equiv.subLeft x).prodCongr (Equiv.subLeft y))

/-- Realise multiplication over `Pre F`.
The simulator samples a uniform pair of openings;
`maskEquiv` identifies their distribution with the real masks. -/
program beaverMult : Realization (Mult F) (Pre F) where
  impl D r := match r with
    | ⟨.mult, (x, y, ())⟩ => mulBeaver x y
  Sim _ := (uniform (F × F)).map (beaverView F)
  real r _ := by
    obtain ⟨⟨⟩, x, y, ⟨⟩⟩ := r
    show dist (Pre F).model (mulBeaver x y) = _
    rw [mulBeaver_dist]
    simp only [weft, Mult.model_eq]
    rw [← uniform_map_equiv (maskEquiv F x y), PMF.bind_map]
    rfl

/-! ## Correlated masks

Sample one uniform `a` and return `(a, a, a²)`.
The triple relation holds,
but subtracting the two openings gives `x − y`.
Inputs `(0, 0)` and `(1, 0)` have the same product and disjoint view supports. -/

/-- Reuse one random value for both masks. -/
def BadMulTriple.corr : Correlation F (F × F × F) := ⟨1, fun x => (x 0, x 0, x 0 * x 0)⟩

/-- A model of the triple interface with correlated masks. -/
noncomputable def BadMulTriple.model : Model (MulTriple.ops F) .ideal PMF :=
  ⟨fun _ => (BadMulTriple.corr F).sample.map fun t => (t, ())⟩

/-- The correlated-mask functionality. -/
abbrev BadMulTriple : Functionality :=
  ⟨MulTriple.ops F, MulTriple.eval F, (· = BadMulTriple.model F), Functionality.unique_eq _⟩

@[simp, weft] theorem BadMulTriple.model_eq : (BadMulTriple F).model = BadMulTriple.model F :=
  Functionality.model_eq rfl

/-- Preprocessing with correlated masks. -/
abbrev BadPre : Hybrid := [Lin F, Reveal F, BadMulTriple F]

/-- Apply the Beaver formula to correlated masks.
Use `mulBeaverFrom` because `BadPre` does not contain `MulTriple`. -/
def mulBeaverBad (x y : F) : Prog (BadPre F).ops .ideal F :=
  mulBeaverFrom (Prog.op (F := BadMulTriple F) ⟨.get, ()⟩) x y

/-- Event list for the correlated-mask implementation. -/
def badView (q : F × F) : List (Event (BadPre F).ops) :=
  [⟨⟨⟨2, by simp⟩, .get⟩, (), ((), (), ()), ()⟩, ⟨⟨⟨0, by simp⟩, .sub⟩, ((), (), ()), (), ()⟩, ⟨⟨⟨1, by simp⟩, .reveal⟩, ((), ()), q.1, ()⟩,
   ⟨⟨⟨0, by simp⟩, .sub⟩, ((), (), ()), (), ()⟩, ⟨⟨⟨1, by simp⟩, .reveal⟩, ((), ()), q.2, ()⟩, ⟨⟨⟨0, by simp⟩, .smul⟩, (q.1, (), ()), (), ()⟩,
   ⟨⟨⟨0, by simp⟩, .smul⟩, (q.2, (), ()), (), ()⟩, ⟨⟨⟨0, by simp⟩, .add⟩, ((), (), ()), (), ()⟩, ⟨⟨⟨0, by simp⟩, .add⟩, ((), (), ()), (), ()⟩,
   ⟨⟨⟨0, by simp⟩, .const⟩, (q.1 * q.2, ()), (), ()⟩, ⟨⟨⟨0, by simp⟩, .add⟩, ((), (), ()), (), ()⟩]

omit [Fintype F] [Inhabited F] in
theorem badBeaver_correct (x y a : F) :
    a * a + (x - a) * a + (y - a) * a + (x - a) * (y - a) = x * y := by ring

/-- The product is correct, while the openings use the same mask. -/
theorem mulBeaver_bad_dist (x y : F) :
    dist (BadPre F).model (mulBeaverBad F x y)
      = (uniform (Fin 1 → F)).bind fun v => pure (x * y, badView F (x - v 0, y - v 0)) := by
  simp only [mulBeaverBad, mulBeaverFrom, badView, sub, reveal, smul, add, const, weft, BadMulTriple.model,
    BadMulTriple.corr]
  congr 1
  funext v
  rw [badBeaver_correct]

/-- Extract the openings from a `BadPre` view. -/
def opened : List (Event (BadPre F).ops) → List F :=
  List.filterMap fun e => match e with
    | ⟨⟨⟨1, _⟩, .reveal⟩, _, out, _⟩ => some out
    | _ => none

/-- Correlated masks prevent simulation from the multiplication event.
The view with openings `[1, 0]` occurs on input `(1, 0)`,
but input `(0, 0)` always produces two equal openings. -/
theorem mulBeaver_bad_not_realizes :
    ¬ ∃ Sim : Event (Mult F).ops → PMF (List (Event (BadPre F).ops)),
      ∀ x y : F, dist (BadPre F).model (mulBeaverBad F x y) = (do
        let p ← (Mult F).model.step ⟨.mult, (x, y, ())⟩
        let s ← Sim ⟨.mult, ((), (), ()), (), p.2⟩
        pure (p.1, s)) := by
  rintro ⟨Sim, h⟩
  have h₀ := h 0 0
  have h₁ := h 1 0
  simp only [mulBeaver_bad_dist, weft, Mult.model_eq, mul_zero] at h₀ h₁
  have same := h₀.trans h₁.symm
  -- Mask zero gives openings `(1, 0)` on input `(1, 0)`.
  have mem₁ : ((0 : F), badView F (1, 0)) ∈
      ((uniform (Fin 1 → F)).bind fun v => PMF.pure ((0 : F), badView F (1 - v 0, 0 - v 0))).support := by
    simp only [PMF.support_bind, PMF.support_pure, Set.mem_iUnion, Set.mem_singleton_iff]
    exact ⟨fun _ => 0, by simp, by simp⟩
  -- Equal simulated distributions would put this view in the support for `(0, 0)`.
  rw [← same] at mem₁
  simp only [PMF.support_bind, PMF.support_pure, Set.mem_iUnion, Set.mem_singleton_iff, Prod.mk.injEq] at mem₁
  obtain ⟨a, -, -, hv⟩ := mem₁
  -- This would equate `[1, 0]` with `[−a, −a]`.
  have h := congrArg (opened F) hv
  change [(1 : F), 0] = [0 - a 0, 0 - a 0] at h
  have h1 := (List.cons.inj h).1
  have h2 := (List.cons.inj (List.cons.inj h).2).1
  exact one_ne_zero (h1.trans h2.symm)
end Privacy

end Weft.Examples.Beaver
