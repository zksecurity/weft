import Weft
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.FieldSimp

/-!
# Inversion by masking

Sample nonzero `s`, open `x·s`, and return the share `s / (x·s)`.
The opened value is uniform among nonzero elements when `x ≠ 0`,
and zero when `x = 0`.

`Invert` returns the inverse without disclosure;
its realisation requires `x ≠ 0`.
`InvertTotal` discloses the zero test,
allowing the same implementation for every input with `0⁻¹ = 0`.

The final caller inverts a `RandNZ` output.
Its validity proof discharges the nonzero precondition using the sampling support.
-/
namespace Weft.Examples.Inversion

section Programs
variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {fs : Hybrid} {D : Domain}

/-- Open `x·s` for nonzero `s`,
then scale `s` by the opened value's reciprocal. -/
def invert [Has (Lin F) fs] [Has (Mult F) fs] [Has (Reveal F) fs] [Has (RandNZ F) fs] (x : D.share F) :
    Prog fs.ops D (D.share F) := do
  let s ← randNZ F
  let v ← mul x s
  let m ← reveal v
  smul m⁻¹ s

/-- Divide by inverting the denominator, then multiplying by the numerator. -/
def divide [Has (Lin F) fs] [Has (Mult F) fs] [Has (Reveal F) fs] [Has (RandNZ F) fs] (a b : D.share F) :
    Prog fs.ops D (D.share F) := do
  let bInv ← invert b
  mul a bInv
end Programs

section
variable (F : Type) [Field F] [Fintype F] [DecidableEq F]

/-- Standard arithmetic with nonzero random shares. -/
abbrev InvHyb : Hybrid := [Lin F, Mult F, Reveal F, RandNZ F]
/-- Zero-cost nonzero masks; multiplication and reveal each take one round. -/
abbrev invMPC : MPC := [(Lin F).priced ⟨0, 0⟩, (Mult F).priced ⟨1, 2⟩, (Reveal F).priced ⟨1, 1⟩, (RandNZ F).priced ⟨0, 0⟩]
/-- Charge one round for sampling a nonzero mask. -/
abbrev invMPC' : MPC := [(Lin F).priced ⟨0, 0⟩, (Mult F).priced ⟨1, 2⟩, (Reveal F).priced ⟨1, 1⟩, (RandNZ F).priced ⟨1, 0⟩]

-- Closed instances over `𝔽₇`, evaluated by the kernel.
instance : Fact (Nat.Prime 7) := ⟨by decide⟩
-- Inversion uses one multiplication and one reveal; division adds a multiplication.
example : commOn (invMPC (ZMod 7)).timed (invert (F := ZMod 7) (fs := (invMPC (ZMod 7)).hybrid) (D := .timed) ⟪3⟫) = 3 := by
  decide +kernel
example : commOn (invMPC (ZMod 7)).timed (divide (F := ZMod 7) (fs := (invMPC (ZMod 7)).hybrid) (D := .timed) ⟪3⟫ ⟪4⟫)
    = 5 := by decide +kernel
-- Mask generation adds to the multiplication and reveal delays.
example : delayOn (invMPC (ZMod 7)).timed (invert (F := ZMod 7) (fs := (invMPC (ZMod 7)).hybrid) (D := .timed) ⟪3⟫) = 2 := by
  decide +kernel
example : delayOn (invMPC' (ZMod 7)).timed (invert (F := ZMod 7) (fs := (invMPC' (ZMod 7)).hybrid) (D := .timed) ⟪3⟫) = 3 := by
  decide +kernel
example : delayOn (invMPC (ZMod 7)).timed (divide (F := ZMod 7) (fs := (invMPC (ZMod 7)).hybrid) (D := .timed) ⟪3⟫ ⟪4⟫)
    = 3 := by decide +kernel

/-- The view of one inversion, as a function of the opened value. -/
def invView (m : F) : List (Event (InvHyb F).ops) :=
  [⟨⟨3, .randNZ⟩, (), (), ()⟩, ⟨⟨1, .mult⟩, ((), (), ()), (), ()⟩, ⟨⟨2, .reveal⟩, ((), ()), m, ()⟩, ⟨⟨0, .smul⟩, (m⁻¹, (), ()), (), ()⟩]

/-- Sample nonzero `s`, reveal `x·s`, and output `s / (x·s)`. -/
theorem invert_dist (x : F) :
    dist (InvHyb F).model (invert (fs := InvHyb F) (D := .ideal) x)
      = (uniform {s : F // s ≠ 0}).bind fun s => pure ((x * s.1)⁻¹ * s.1, invView F (x * s.1)) := by
  simp only [invert, invView, randNZ, mul, reveal, smul, weft]
  rfl

/-- For nonzero `x`, every supported mask gives output `x⁻¹`. -/
theorem invert_correct (x : F) (hx : x ≠ 0) :
    Prod.fst <$> dist (InvHyb F).model (invert (fs := InvHyb F) (D := .ideal) x) = pure x⁻¹ := by
  rw [invert_dist]
  have : ∀ s : {s : F // s ≠ 0}, s.1⁻¹ * x⁻¹ * s.1 = x⁻¹ := fun s => by
    have := s.2; field_simp
  simp [PMF.monad_map_eq_map, PMF.map_bind, PMF.pure_map, PMF.monad_pure_eq_pure, this, PMF.bind_const]

/-! ## Inversion without disclosure -/

/-- Return the inverse as a share without additional disclosure. -/
abbrev Invert : Functionality :=
  .ofEval ⟨Unit, fun _ => [.share F], fun _ => .share F, fun _ => Unit⟩
    ⟨fun r => pure (r.args.1⁻¹, ())⟩

/-- Realise `Invert` for nonzero inputs.
Multiplication by `x` permutes the nonzero elements,
so the simulator can sample a fresh nonzero opening. -/
program invertReal : Realization (Invert F) (InvHyb F) where
  impl D r := invert r.args.1
  Pre r := r.args.1 ≠ 0
  Sim _ := (uniform {t : F // t ≠ 0}).map fun t => invView F t.1
  real r hx := by
    obtain ⟨⟨⟩, x, ⟨⟩⟩ := r
    show dist (InvHyb F).model (invert x) = _
    rw [invert_dist]
    -- Every nonzero mask gives the same output.
    have out : ∀ s : {s : F // s ≠ 0}, (x * s.1)⁻¹ * s.1 = x⁻¹ := fun s => by
      have := s.2; field_simp
    simp only [out, weft, Functionality.ofEval_model]
    -- Multiplication by nonzero `x` permutes the mask space.
    let e : {s : F // s ≠ 0} ≃ {t : F // t ≠ 0} :=
      (Equiv.mulLeft₀ x hx).subtypeEquiv fun s => by simp [hx]
    conv_rhs => rw [← uniform_map_equiv e, PMF.bind_map]
    rfl

/-! ## Inversion with a disclosed zero test -/

/-- Return `x⁻¹` as a share and disclose whether `x = 0`. -/
abbrev InvertTotal : Functionality :=
  .ofEval ⟨Unit, fun _ => [.share F], fun _ => .share F, fun _ => Bool⟩
    ⟨fun r => pure (r.args.1⁻¹, decide (r.args.1 = 0))⟩

/-- Simulate every input using the disclosed zero test.
The opening is zero in the zero case and uniform nonzero otherwise. -/
program invertTotalReal : Realization (InvertTotal F) (InvHyb F) where
  impl D r := invert r.args.1
  Sim e := if e.leak then pure (invView F 0) else (uniform {t : F // t ≠ 0}).map fun t => invView F t.1
  real r _ := by
    obtain ⟨⟨⟩, x, ⟨⟩⟩ := r
    show dist (InvHyb F).model (invert x) = _
    rw [invert_dist]
    by_cases hx : x = 0
    · subst hx
      simp only [zero_mul, inv_zero, PMF.bind_const, weft, Functionality.ofEval_model, decide_true, if_true]
    · have out : ∀ s : {s : F // s ≠ 0}, (x * s.1)⁻¹ * s.1 = x⁻¹ := fun s => by
        have := s.2; field_simp
      simp only [out, weft, Functionality.ofEval_model, hx, decide_false, Bool.false_eq_true, if_false]
      let e : {s : F // s ≠ 0} ≃ {t : F // t ≠ 0} :=
        (Equiv.mulLeft₀ x hx).subtypeEquiv fun s => by simp [hx]
      conv_rhs => rw [← uniform_map_equiv e, PMF.bind_map]
      rfl

/-- Request inversion of a fresh nonzero share. -/
def invertFresh {fs : Hybrid} {D : Domain} [Has (Invert F) fs] [Has (RandNZ F) fs] : Prog fs.ops D (D.share F) := do
  let r ← randNZ F
  Prog.op (F := Invert F) ⟨(), (r, ())⟩

/-- Inversion and nonzero sampling. -/
abbrev CallerHyb : Hybrid := [Invert F, RandNZ F]

/-- Every inversion request has a nonzero operand,
since it comes from the support of `RandNZ`. -/
theorem invertFresh_valid :
    Valid (CallerHyb F).model (fun r => match r with
        | ⟨⟨⟨0, _⟩, _⟩, a⟩ => a.1 ≠ 0
        | _ => True)
      (invertFresh F (fs := CallerHyb F) (D := .ideal)) := by
  refine .call _ _ trivial fun z hz => ?_
  refine .call _ _ ?_ fun _ _ => .pure _
  -- Recover the nonzero witness from the sampling support.
  have hz' : z ∈ ((RandNZ F).model.step ⟨.randNZ, ()⟩).support := hz
  rw [RandNZ.model_eq] at hz'
  simp only [RandNZ.model, PMF.support_map, PMF.support_uniformOfFintype, Set.mem_image] at hz'
  obtain ⟨t, -, rfl⟩ := hz'
  exact t.2

end

end Weft.Examples.Inversion
