import Weft

/-!
# Multiplication from Beaver triples

The flagship example: a program written against three functionalities
only (linear operations, `reveal`, and a `MulTriple` box handing out
`(a, b, a·b)`), and the four things one proves about it.

* **Correctness**: the output is `x·y` with certainty.
* **Communication**: two openings, on an MPC that prices them.
* **Rounds**: one, since the two openings are independent (nothing says
  so; the timed domain sees it).
* **Privacy**: the program realises the multiplication functionality over
  the preprocessing hybrid.  The simulator draws a fresh uniform pair and
  presents it as the two opened values; the proof is the mask lemma on
  `(a, b) ↦ (x − a, y − b)`, a bijection of `F²`.

The privacy argument rests on one fact about the *pair* `(a, b)`: it is
uniform on `F²`.  The last section shows a wrong model of the triple box
for which that is exactly what fails: `a` and `b` each uniform, `c = a·b`
as promised, the program still correct, and the two opened values
together publish `x − y`.
-/
namespace Weft.Examples.Beaver

section Programs
variable {F : Type} [Add F] [Mul F] [Sub F] [Fintype F] [Inhabited F] {fs : Hybrid} {D : Domain}

/-- `x · y` from a triple obtained by `triple`: open the masked inputs, then
only linear operations.  Written once, for any domain, any hybrid offering
linear operations and reveal, and any source of triples. -/
def mulBeaverFrom [Has (Lin F) fs] [Has (Reveal F) fs] (triple : Prog fs.ops D (D.sh F × D.sh F × D.sh F))
    (x y : D.sh F) : Prog fs.ops D (D.sh F) := do
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

/-- Beaver multiplication with the triple from the `MulTriple` box. -/
def mulBeaver [Has (Lin F) fs] [Has (Reveal F) fs] [Has (MulTriple F) fs] (x y : D.sh F) : Prog fs.ops D (D.sh F) :=
  mulBeaverFrom (mulTriple F) x y

/-- Two multiplications in sequence, two triples. -/
def mul3Beaver [Has (Lin F) fs] [Has (Reveal F) fs] [Has (MulTriple F) fs] (x y z : D.sh F) :
    Prog fs.ops D (D.sh F) := do
  let xy ← mulBeaver x y
  mulBeaver xy z
end Programs

/-! ## Evaluation: correctness, view, communication, rounds -/

section MPCs
variable (F : Type) [Add F] [Mul F] [Sub F] [Fintype F] [Inhabited F]
/-- A preprocessing MPC: triples are free (precomputed), openings cost one round and one unit. -/
abbrev preMPC : MPC := [MPC.const (Lin F) ⟨0, 0⟩, MPC.const (Reveal F) ⟨1, 1⟩, MPC.const (MulTriple F) ⟨0, 0⟩]
/-- The same MPC generating triples online, in two rounds. -/
abbrev preOnline : MPC := [MPC.const (Lin F) ⟨0, 0⟩, MPC.const (Reveal F) ⟨1, 1⟩, MPC.const (MulTriple F) ⟨2, 3⟩]
end MPCs

section Evaluation
variable (F : Type) [Add F] [Mul F] [Sub F] [Fintype F] [Inhabited F]

/-- The view of one Beaver multiplication, as a function of the two opened values. -/
def beaverView (q : F × F) : List (Event (Pre F).ops) :=
  [⟨Pre.triple F, ((), (), ()), ()⟩, ⟨Pre.lin F .sub, (), ()⟩, ⟨Pre.reveal F, q.1, ()⟩, ⟨Pre.lin F .sub, (), ()⟩,
   ⟨Pre.reveal F, q.2, ()⟩, ⟨Pre.lin F (.smul q.1), (), ()⟩, ⟨Pre.lin F (.smul q.2), (), ()⟩,
   ⟨Pre.lin F .add, (), ()⟩, ⟨Pre.lin F .add, (), ()⟩, ⟨Pre.lin F (.const (q.1 * q.2)), (), ()⟩,
   ⟨Pre.lin F .add, (), ()⟩]

-- The view (the two opened values and the operations around them) is what `mulBeaver_dist`
-- below computes exactly, as a distribution, under the real model.

-- **Communication**: two openings.
example : cost (preMPC (Fin 7)).eval (preMPC (Fin 7)).comm
    (mulBeaver (F := Fin 7) (fs := (preMPC (Fin 7)).hybrid) (D := .ideal) 3 4) = 2 := by decide +kernel
end Evaluation

section Closed
/-! All closed instances over `ℤ/7` are evaluated by the kernel with `decide +kernel`: `rfl`
runs the interpreter inside the elaborator, which is an order of magnitude slower at this size. -/

-- ...and with online triples, the triple's three units as well.
example : cost (preOnline (Fin 7)).eval (preOnline (Fin 7)).comm
    (mulBeaver (F := Fin 7) (fs := (preOnline (Fin 7)).hybrid) (D := .ideal) 3 4) = 5 := by decide +kernel
-- **Rounds**: one, since the two openings are independent; three when the triple takes two rounds.
example : delayOn (preMPC (Fin 7)).timed
    (mulBeaver (F := Fin 7) (fs := (preMPC (Fin 7)).hybrid) (D := .timed) ⟪3⟫ ⟪4⟫) = 1 := by decide +kernel
example : delayOn (preOnline (Fin 7)).timed
    (mulBeaver (F := Fin 7) (fs := (preOnline (Fin 7)).hybrid) (D := .timed) ⟪3⟫ ⟪4⟫) = 3 := by decide +kernel
-- Two chained multiplications: two rounds, four openings.
example : delayOn (preMPC (Fin 7)).timed
    (mul3Beaver (F := Fin 7) (fs := (preMPC (Fin 7)).hybrid) (D := .timed) ⟪3⟫ ⟪4⟫ ⟪5⟫) = 2 := by
  decide +kernel
example : cost (preMPC (Fin 7)).eval (preMPC (Fin 7)).comm
    (mul3Beaver (F := Fin 7) (fs := (preMPC (Fin 7)).hybrid) (D := .ideal) 3 4 5) = 4 := by
  decide +kernel
end Closed

/-! ## The semantics, and privacy -/

section Privacy
variable (F : Type) [Field F] [Fintype F] [Inhabited F]

omit [Fintype F] [Inhabited F] in
theorem beaver_correct (x y : F) (v : Fin 2 → F) :
    v 0 * v 1 + (x - v 0) * v 1 + (y - v 1) * v 0 + (x - v 0) * (y - v 1) = x * y := by ring

/-- **The semantics of `mulBeaver`**: the triple is one uniform draw `v` from
`F²`, the output is `x·y` for every `v`, and the view is a function of the
two opened values `(x − v 0, y − v 1)`. -/
theorem mulBeaver_dist (x y : F) :
    dist (Pre F).model (mulBeaver (fs := Pre F) (D := .ideal) x y)
      = (uniform (Fin 2 → F)).bind fun v => pure (x * y, beaverView F (x - v 0, y - v 1)) := by
  simp only [mulBeaver, mulBeaverFrom, beaverView, mulTriple, sub, reveal, smul, add, const, weft]
  congr 1
  funext v
  rw [beaver_correct]
  rfl

/-- **Correctness is perfect**: the output is `x·y` with certainty. -/
theorem mulBeaver_correct (x y : F) :
    Prod.fst <$> dist (Pre F).model (mulBeaver (fs := Pre F) (D := .ideal) x y) = pure (x * y) := by
  rw [mulBeaver_dist]
  simp [PMF.monad_map_eq_map, PMF.monad_pure_eq_pure, PMF.map_bind, PMF.pure_map, PMF.bind_const]

/-- The masks: `(a, b) ↦ (x − a, y − b)` is a bijection of `F²`. -/
def maskEquiv (x y : F) : (Fin 2 → F) ≃ F × F :=
  (piFinTwoEquiv fun _ => F).trans ((Equiv.subLeft x).prodCongr (Equiv.subLeft y))

/-- **Privacy.**  Beaver multiplication realises the multiplication
functionality over the preprocessing hybrid.  The simulator, given the
event `(mult, (), ())`, draws a fresh uniform pair and presents the Beaver
view of it.  The proof: unfold the run, then the mask lemma. -/
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

/-! ## The counterexample: masks that are each uniform, but not jointly

A "triple" box that draws one coin `a` and hands out `(a, a, a²)`.  Each
component is a correct Beaver triple coordinate-wise: `a` is uniform, `b`
is uniform, `c = a·b`.  `mulBeaver` is still perfectly correct on it.  But
the opened pair `(x − a, y − a)` determines `x − y`, so the program does
not realise `Mult`: the same output `0` arises from `(0, 0)` and `(1, 0)`
with disjoint sets of possible views. -/

/-- The degenerate correlation: one coin, used twice. -/
def BadMulTriple.corr : Correlation F (F × F × F) := ⟨1, fun x => (x 0, x 0, x 0 * x 0)⟩

/-- A *wrong model* of the `MulTriple` interface: the only way to state the counterexample. -/
noncomputable def BadMulTriple.model : Model (MulTriple.ops F) .ideal PMF :=
  ⟨fun _ => (BadMulTriple.corr F).sample.map fun t => (t, ())⟩

/-- The wrong functionality, under its own name. -/
abbrev BadMulTriple : Functionality :=
  ⟨MulTriple.ops F, MulTriple.eval F, (· = BadMulTriple.model F), Functionality.unique_eq _, MulTriple.timed F⟩

@[simp, weft] theorem BadMulTriple.model_eq : (BadMulTriple F).model = BadMulTriple.model F :=
  Functionality.model_eq rfl

/-- The preprocessing hybrid with the wrong triple box. -/
abbrev BadPre : Hybrid := [Lin F, Reveal F, BadMulTriple F]

/-- Beaver multiplication with the triple from the wrong box.  (`mulBeaver` itself cannot
be run here: its type names `MulTriple F`, and the hybrid does not offer it.  The program's
meaning is fixed by the functionalities it names.) -/
def mulBeaverBad (x y : F) : Prog (BadPre F).ops .ideal F :=
  mulBeaverFrom (Prog.op (F := BadMulTriple F) ⟨.get, ()⟩) x y

/-- The view of a Beaver multiplication over the wrong box, as a function of the two opened values. -/
def badView (q : F × F) : List (Event (BadPre F).ops) :=
  [⟨⟨⟨2, by simp⟩, .get⟩, ((), (), ()), ()⟩, ⟨⟨⟨0, by simp⟩, .sub⟩, (), ()⟩, ⟨⟨⟨1, by simp⟩, .reveal⟩, q.1, ()⟩,
   ⟨⟨⟨0, by simp⟩, .sub⟩, (), ()⟩, ⟨⟨⟨1, by simp⟩, .reveal⟩, q.2, ()⟩, ⟨⟨⟨0, by simp⟩, .smul q.1⟩, (), ()⟩,
   ⟨⟨⟨0, by simp⟩, .smul q.2⟩, (), ()⟩, ⟨⟨⟨0, by simp⟩, .add⟩, (), ()⟩, ⟨⟨⟨0, by simp⟩, .add⟩, (), ()⟩,
   ⟨⟨⟨0, by simp⟩, .const (q.1 * q.2)⟩, (), ()⟩, ⟨⟨⟨0, by simp⟩, .add⟩, (), ()⟩]

omit [Fintype F] [Inhabited F] in
theorem badBeaver_correct (x y a : F) :
    a * a + (x - a) * a + (y - a) * a + (x - a) * (y - a) = x * y := by ring

/-- Still correct: the output is `x·y`; the view is that of the opened pair `(x − a, y − a)`. -/
theorem mulBeaver_bad_dist (x y : F) :
    dist (BadPre F).model (mulBeaverBad F x y)
      = (uniform (Fin 1 → F)).bind fun v => pure (x * y, badView F (x - v 0, y - v 0)) := by
  simp only [mulBeaverBad, mulBeaverFrom, badView, sub, reveal, smul, add, const, weft, BadMulTriple.model,
    BadMulTriple.corr]
  congr 1
  funext v
  rw [badBeaver_correct]

/-- The values opened by a run over the wrong box. -/
def opened : List (Event (BadPre F).ops) → List F :=
  List.filterMap fun e => match e with
    | ⟨⟨⟨1, _⟩, .reveal⟩, out, _⟩ => some out
    | _ => none

/-- **Not private.**  No simulator that sees only the event can produce the
Beaver view: on the inputs `(0, 0)` and `(1, 0)` the output is `0` with
certainty and the event is the same, so the two real views would have to be
the same distribution; but `[1, 0]` is a possible pair of openings for
`(1, 0)` (mask `a = 0`) and for `(0, 0)` every opened pair is `(−a, −a)`. -/
theorem mulBeaver_bad_not_realizes :
    ¬ ∃ Sim : Event (Mult F).ops → PMF (List (Event (BadPre F).ops)),
      ∀ x y : F, dist (BadPre F).model (mulBeaverBad F x y) = (do
        let p ← (Mult F).model.step ⟨.mult, (x, y, ())⟩
        let s ← Sim ⟨.mult, (), p.2⟩
        pure (p.1, s)) := by
  rintro ⟨Sim, h⟩
  have h₀ := h 0 0
  have h₁ := h 1 0
  simp only [mulBeaver_bad_dist, weft, Mult.model_eq, mul_zero] at h₀ h₁
  have same := h₀.trans h₁.symm
  -- the view of the opened pair `(1, 0)` is possible for `(1, 0)` (mask `a = 0`) ...
  have mem₁ : ((0 : F), badView F (1, 0)) ∈
      ((uniform (Fin 1 → F)).bind fun v => PMF.pure ((0 : F), badView F (1 - v 0, 0 - v 0))).support := by
    simp only [PMF.support_bind, PMF.support_pure, Set.mem_iUnion, Set.mem_singleton_iff]
    exact ⟨fun _ => 0, by simp, by simp⟩
  -- ... hence, by `same`, for `(0, 0)`: but there every opened pair is `(−a, −a)`
  rw [← same] at mem₁
  simp only [PMF.support_bind, PMF.support_pure, Set.mem_iUnion, Set.mem_singleton_iff, Prod.mk.injEq] at mem₁
  obtain ⟨a, -, -, hv⟩ := mem₁
  -- the opened values would be `[1, 0]` and `[−a, −a]` at once
  have h := congrArg (opened F) hv
  simp [opened, badView] at h
  obtain ⟨h1, h2⟩ := h
  rw [h2, neg_zero] at h1
  exact one_ne_zero h1
end Privacy

end Weft.Examples.Beaver
