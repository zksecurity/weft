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
-/
namespace Weft.Examples.Beaver

section Programs
variable {F : Type} [Add F] [Mul F] [Sub F] [Fintype F] [Inhabited F] {fs : Hybrid} {D : Domain}

/-- Multiply two shares using the independent masks supplied by `MulTriple`. -/
def mulBeaver
    [Has (Const F) fs]
    [Has (Addition F) fs]
    [Has (Subtraction F) fs]
    [Has (Smul F) fs]
    [Has (Reveal F) fs]
    [Has (MulTriple F) fs]
    (x y : D.share F) :
    Prog fs.ops D (D.share F) := do
  let (a, b, c) ← mulTriple F
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

end Programs

/-! ## Evaluation and costs -/

section MPCs
variable (F : Type) [Add F] [Mul F] [Sub F] [Fintype F] [Inhabited F]
/-- Precomputed triples are free; each opening costs one round and one unit. -/
abbrev preMPC : MPC := [
  (Const F).priced ⟨0, 0⟩,
  (Addition F).priced ⟨0, 0⟩,
  (Subtraction F).priced ⟨0, 0⟩,
  (Smul F).priced ⟨0, 0⟩,
  (Reveal F).priced ⟨1, 1⟩,
  (MulTriple F).priced ⟨0, 0⟩]
/-- Charge two rounds and three units for online triple generation. -/
abbrev preOnline : MPC := [
  (Const F).priced ⟨0, 0⟩,
  (Addition F).priced ⟨0, 0⟩,
  (Subtraction F).priced ⟨0, 0⟩,
  (Smul F).priced ⟨0, 0⟩,
  (Reveal F).priced ⟨1, 1⟩,
  (MulTriple F).priced ⟨2, 3⟩]
end MPCs

section Evaluation
variable (F : Type) [Add F] [Mul F] [Sub F] [Fintype F] [Inhabited F]

/-- The view of one Beaver multiplication, as a function of the two opened values. -/
def beaverView (q : F × F) : List (Event (Pre F).ops) :=
  [event[MulTriple F] (),
   event[Subtraction F] (),
   event[Reveal F] q.1,
   event[Subtraction F] (),
   event[Reveal F] q.2,
   event[Smul F] q.1,
   event[Smul F] q.2,
   event[Addition F] (),
   event[Addition F] (),
   event[Const F] (q.1 * q.2),
   event[Addition F] ()]

-- `mulBeaver_dist` samples the two masked inputs,
-- then applies `beaverView` to obtain the view.

-- Two openings at one communication unit each.
example :
    commOn (preMPC (Fin 7)).timed
      (mulBeaver (F := Fin 7) (fs := (preMPC (Fin 7)).hybrid) (D := .timed) ⟪3⟫ ⟪4⟫)
      = 2 := by decide +kernel
end Evaluation

section Closed
/-! Use `decide +kernel` for the closed `Fin 7` instances.
It avoids the elaborator's reduction overhead when evaluating these programs. -/

-- Online generation adds the triple's three communication units.
example :
    commOn (preOnline (Fin 7)).timed
      (mulBeaver (F := Fin 7) (fs := (preOnline (Fin 7)).hybrid) (D := .timed) ⟪3⟫ ⟪4⟫)
      = 5 := by decide +kernel
-- Independent openings take one round after the triple is available.
example :
    delayOn (preMPC (Fin 7)).timed
      (mulBeaver (F := Fin 7) (fs := (preMPC (Fin 7)).hybrid) (D := .timed) ⟪3⟫ ⟪4⟫)
      = 1 := by decide +kernel
example :
    delayOn (preOnline (Fin 7)).timed
      (mulBeaver (F := Fin 7) (fs := (preOnline (Fin 7)).hybrid) (D := .timed) ⟪3⟫ ⟪4⟫)
      = 3 := by decide +kernel
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
      = (uniform (Fin 2 → F)).bind fun v =>
          pure (x * y, beaverView F (x - v 0, y - v 1)) := by
  unfold mulBeaver
  simp only [
    beaverView,
    mulTriple,
    sub,
    reveal,
    smul,
    add,
    const,
    weft
  ]
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
    | (x, y, ()) => mulBeaver x y
  Sim _ := (uniform (F × F)).map (beaverView F)
  real r _ := by
    obtain ⟨x, y, ⟨⟩⟩ := r
    show dist (Pre F).model (mulBeaver x y) = _
    rw [mulBeaver_dist]
    simp only [weft, Mult.model_eq]
    rw [← uniform_map_equiv (maskEquiv F x y), PMF.bind_map]
    rfl

/-- Beaver multiplication, as a statistical realisation with error zero. -/
noncomputable def beaverStat : RealizationStat (Mult F) (Pre F) := (beaverMult F).toStat

theorem beaverStat_error : (beaverStat F).ε = 0 := rfl

end Privacy

end Weft.Examples.Beaver
