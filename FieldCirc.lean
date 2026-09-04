import Features
import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.FieldSimp

/-!
# Circuits over a field

The algebra of the clear type is a property of the domain, `D.F`, not a
feature of the MPC.  A circuit that needs it says so with a class
constraint next to its `Has` bounds:

    def f {D : Domain} [Field D.F] {M : MPC} [Has .lin M] [Has .mult M] … : Circ' D M …

This is Mathlib's `Field`.  Ring-only MPCs
(`ℤ/2^k`) simply do not satisfy `[Field D.F]`, and circuits that only ask
for `[CommRing D.F]` run on both.
-/
namespace Glean.FS
open Glean

-- Fields are Mathlib's `Field`.

section Ops
variable {D : Domain} {M : MPC}
def smul [Has .lin M] (x : D.F) (a : D.S) : Circ' D M D.S := op .lin (Lin.smul x a)
def rand [Has .rand M] : Circ' D M D.S := op .rand Rand.rand
/-- A uniformly random *nonzero* share: the functionality guarantees the mask is invertible. -/
def randNZ [Has .randNZ M] : Circ' D M D.S := op .randNZ RandNZ.randNZ
end Ops

section
variable {D : Domain} [Field D.F] {M : MPC}

/-- Free linear sum. -/
def sumAll [Has .lin M] : List D.S → Circ' D M D.S
  | [] => const (0 : D.F)
  | [x] => pure x
  | x :: xs => do let s ← sumAll xs; add x s

/-- Lagrange interpolation at a public point `x` through secret values `ys`
at public nodes.  The coefficients need division, computed in the clear;
the combination is linear.  Zero delay on every MPC with `lin`. -/
def interpolate [DecidableEq D.F] [Has .lin M] (nodes : List D.F) (ys : List D.S) (x : D.F) :
    Circ' D M D.S := do
  let coeff (xi : D.F) : D.F :=
    (nodes.filter (· ≠ xi)).foldl (fun acc xj => acc * ((x - xj) / (xi - xj))) 1
  let terms ← (nodes.zip ys).mapM fun p => smul (coeff p.1) p.2
  sumAll terms

/-- Field inversion by masking: `1/x = s / open(x·s)` for a random nonzero
`s`.  Needs division in the clear, and coins.  Two delay: one multiplication,
one opening.  The mask comes from `randNZ`, so correctness is perfect: no
"bad coins" to count. -/
def invert [Has .lin M] [Has .mult M] [Has .randNZ M] [Has .reveal M] (x : D.S) : Circ' D M D.S := do
  let s ← randNZ
  let v ← mul x s
  let m ← reveal v
  smul (1 / m) s

/-- Division `a / b` = `a · (1/b)`: one more round. -/
def divide [Has .lin M] [Has .mult M] [Has .randNZ M] [Has .reveal M] (a b : D.S) : Circ' D M D.S := do
  let bInv ← invert b
  mul a bInv
end

/-! ## What the user proves -/

section
variable (F : Type) [Field F] [DecidableEq F] [LT F] [DecidableLT F] [Fintype F] [Inhabited F]
local notation "𝕀" => Domain.ideal F

-- Communication and delay are field-independent and close by evaluation.
local notation "𝕋" => Domain.timed F
example (x : F) :
    cost (honestMajority.eval F) honestMajority.commModel (invert (D := 𝕀) x) = 3 := rfl
example (x : F) :
    delayOn (honestMajority.timed F) (invert (D := 𝕋) ⟨x, 0⟩) = 2 := rfl
example (a b : F) :
    cost (honestMajority.eval F) honestMajority.commModel (divide (D := 𝕀) a b) = 5 := rfl
example (a b : F) :
    delayOn (honestMajority.timed F) (divide (D := 𝕋) ⟨a, 0⟩ ⟨b, 0⟩) = 3 := rfl
example (x₀ x₁ x₂ y₀ y₁ y₂ x : F) :
    cost (honestMajority.eval F) honestMajority.commModel
      (interpolate (D := 𝕀) [x₀, x₁, x₂] [y₀, y₁, y₂] x) = 0 := rfl
example (x₀ x₁ x₂ y₀ y₁ y₂ x : F) :
    delayOn (honestMajority.timed F) (interpolate (D := 𝕋) [x₀, x₁, x₂] [⟨y₀, 0⟩, ⟨y₁, 0⟩, ⟨y₂, 0⟩] x) = 0 := rfl

omit [Inhabited F] in
/-- The semantics of `invert`: a uniform nonzero mask `s`, the opened value `x·s`,
and the output `s / (x·s)`. -/
theorem invert_dist (x : F) :
    dist (honestMajority.ideal F) (invert (D := 𝕀) x)
      = (uniform {s : F // s ≠ 0}).bind fun s => pure ((x * s.1)⁻¹ * s.1, [x * s.1]) := by
  simp [dist, invert, MPC.ideal, Feature.ideal, Lin.ideal, Mult.ideal, Reveal.ideal, RandNZ.ideal,
    randNZ, mul, reveal, smul, FS.op, run, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    PMF.monad_map_eq_map, PMF.map_bind, PMF.pure_map, PMF.bind_map, Function.comp_def, mul_comm]

omit [Inhabited F] in
-- Correctness is perfect and is field algebra: `s / (x·s) = 1/x` when `x ≠ 0`
-- and `s ≠ 0`; the second is guaranteed by the functionality.
theorem invert_correct (x : F) (hx : x ≠ 0) :
    Prod.fst <$> dist (honestMajority.ideal F) (invert (D := 𝕀) x) = pure x⁻¹ := by
  rw [invert_dist]
  have : ∀ s : {s : F // s ≠ 0}, s.1⁻¹ * x⁻¹ * s.1 = x⁻¹ := fun s => by
    have := s.2; field_simp
  simp [PMF.monad_map_eq_map, PMF.map_bind, PMF.pure_map, PMF.monad_pure_eq_pure, this, PMF.bind_const]
end

end Glean.FS
