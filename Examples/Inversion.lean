import Weft
import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.FieldSimp

/-!
# Inversion by masking: assumptions belong to realisations

`1/x = s / open(x·s)` for a random nonzero mask `s`.  The functionality it
implements can be stated in two honest ways (report, Issue 4), both under
their own names:

* **`Invert F`, silent**: returns `⟦x⁻¹⟧` and declares nothing.  The
  program realises it only for `x ≠ 0`; on `x = 0` the opened value is `0`
  and the run is not simulatable from nothing.  So the realisation carries
  the precondition, and a caller discharges it by `Valid`: every request it
  issues, on the support of its ideal run, has a nonzero operand.  The
  example caller inverts the output of `randNZ`, whose support is the
  nonzero elements.
* **`InvertTotal F`, total**: returns `⟦x⁻¹⟧` (with `0⁻¹ = 0`) and
  discloses whether `x = 0`.  The same program realises it with no
  precondition; the caller pays the declared disclosure instead.

Correctness is perfect in both cases: the mask comes from `RandNZ`, so
the functionality, not luck, guarantees it is invertible.
-/
namespace Weft.Examples.Inversion

section Programs
variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {fs : Hybrid} {D : Domain}

/-- Inversion by masking, polymorphic in the domain: the same definition is
run at the ideal domain for the certificate and at the timed domain for its
delay. -/
def invert [Has (Lin F) fs] [Has (Mult F) fs] [Has (Reveal F) fs] [Has (RandNZ F) fs] (x : D.sh F) :
    Prog fs.ops D (D.sh F) := do
  let s ← randNZ F
  let v ← mul x s
  let m ← reveal v
  smul m⁻¹ s

/-- Division `a / b = a · (1/b)`: one more round. -/
def divide [Has (Lin F) fs] [Has (Mult F) fs] [Has (Reveal F) fs] [Has (RandNZ F) fs] (a b : D.sh F) :
    Prog fs.ops D (D.sh F) := do
  let bInv ← invert b
  mul a bInv
end Programs

section
variable (F : Type) [Field F] [Fintype F] [DecidableEq F]

/-- The hybrid with a nonzero random share. -/
abbrev InvHyb : Hybrid := [Lin F, Mult F, Reveal F, RandNZ F]
/-- ...priced: multiplication and reveal one round each, random shares free (PRSS). -/
abbrev invMPC : MPC := [MPC.const (Lin F) ⟨0, 0⟩, MPC.const (Mult F) ⟨1, 2⟩, MPC.const (Reveal F) ⟨1, 1⟩,
  MPC.const (RandNZ F) ⟨0, 0⟩]
/-- ...and an MPC where a random share costs a round. -/
abbrev invMPC' : MPC := [MPC.const (Lin F) ⟨0, 0⟩, MPC.const (Mult F) ⟨1, 2⟩, MPC.const (Reveal F) ⟨1, 1⟩,
  MPC.const (RandNZ F) ⟨1, 0⟩]

-- **Communication**: one multiplication and one reveal.
example (x : F) : cost (invMPC F).eval (invMPC F).comm (invert (fs := (invMPC F).hybrid) (D := .ideal) x) = 3 := rfl
example (a b : F) : cost (invMPC F).eval (invMPC F).comm (divide (fs := (invMPC F).hybrid) (D := .ideal) a b) = 5 := rfl
-- **Rounds**: two where random shares are free, three where they cost a round; division adds one.
example (x : F) : delayOn (invMPC F).timed (invert (fs := (invMPC F).hybrid) (D := .timed) ⟪x⟫) = 2 := rfl
example (x : F) : delayOn (invMPC' F).timed (invert (fs := (invMPC' F).hybrid) (D := .timed) ⟪x⟫) = 3 := rfl
example (a b : F) : delayOn (invMPC F).timed (divide (fs := (invMPC F).hybrid) (D := .timed) ⟪a⟫ ⟪b⟫) = 3 := rfl

/-- The view of one inversion, as a function of the opened value. -/
def invView (m : F) : List (Event (InvHyb F).ops) :=
  [⟨⟨3, .randNZ⟩, (), ()⟩, ⟨⟨1, .mult⟩, (), ()⟩, ⟨⟨2, .reveal⟩, m, ()⟩, ⟨⟨0, .smul m⁻¹⟩, (), ()⟩]

/-- **The semantics of `invert`**: a uniform nonzero mask `s`, the opened
value `x·s`, and the output `s / (x·s)`. -/
theorem invert_dist (x : F) :
    dist (InvHyb F).model (invert (fs := InvHyb F) (D := .ideal) x)
      = (uniform {s : F // s ≠ 0}).bind fun s => pure ((x * s.1)⁻¹ * s.1, invView F (x * s.1)) := by
  simp only [invert, invView, randNZ, mul, reveal, smul, weft]
  rfl

/-- **Correctness is perfect**: `s / (x·s) = x⁻¹` when `x ≠ 0`, for every mask. -/
theorem invert_correct (x : F) (hx : x ≠ 0) :
    Prod.fst <$> dist (InvHyb F).model (invert (fs := InvHyb F) (D := .ideal) x) = pure x⁻¹ := by
  rw [invert_dist]
  have : ∀ s : {s : F // s ≠ 0}, s.1⁻¹ * x⁻¹ * s.1 = x⁻¹ := fun s => by
    have := s.2; field_simp
  simp [PMF.monad_map_eq_map, PMF.map_bind, PMF.pure_map, PMF.monad_pure_eq_pure, this, PMF.bind_const]

/-! ## The silent contract, with a precondition -/

/-- Inversion, silent: returns `⟦x⁻¹⟧`, declares nothing. -/
abbrev Invert : Functionality :=
  .ofEval ⟨Unit, fun _ => [F], fun _ => .share F, fun _ => Unit, fun _ => false, fun _ => false⟩
    ⟨fun r => pure (r.args.1⁻¹, ())⟩

/-- **Inversion by masking realises silent inversion for `x ≠ 0`.**  The
simulator draws a fresh uniform nonzero element and presents it as the
opened value: `s ↦ x·s` is a bijection of the nonzero elements. -/
program invertReal : Realization (Invert F) (InvHyb F) where
  impl D r := invert r.args.1
  Pre r := r.args.1 ≠ 0
  Sim _ := (uniform {t : F // t ≠ 0}).map fun t => invView F t.1
  real r hx := by
    obtain ⟨⟨⟩, x, ⟨⟩⟩ := r
    show dist (InvHyb F).model (invert x) = _
    rw [invert_dist]
    -- the output is a point: `s / (x·s) = x⁻¹` on the whole support
    have out : ∀ s : {s : F // s ≠ 0}, (x * s.1)⁻¹ * s.1 = x⁻¹ := fun s => by
      have := s.2; field_simp
    simp only [out, weft, Functionality.ofEval_model]
    -- the mask: `s ↦ x·s` is a bijection of the nonzero elements
    let e : {s : F // s ≠ 0} ≃ {t : F // t ≠ 0} :=
      (Equiv.mulLeft₀ x hx).subtypeEquiv fun s => by simp [hx]
    conv_rhs => rw [← uniform_map_equiv e, PMF.bind_map]
    rfl

/-! ## The total contract, with a declared disclosure -/

/-- Inversion, total: returns `⟦x⁻¹⟧` (with `0⁻¹ = 0`) and discloses whether `x = 0`. -/
abbrev InvertTotal : Functionality :=
  .ofEval ⟨Unit, fun _ => [F], fun _ => .share F, fun _ => Bool, fun _ => false, fun _ => false⟩
    ⟨fun r => pure (r.args.1⁻¹, decide (r.args.1 = 0))⟩

/-- **The same program realises total inversion with no precondition.**  The
simulator reads the zero test off the event: on `x = 0` the opened value is
`0`, otherwise it is a fresh uniform nonzero element, as before. -/
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

/-- A caller that inverts a fresh nonzero share: `randNZ`, then `invert`. -/
def invertFresh {fs : Hybrid} {D : Domain} [Has (Invert F) fs] [Has (RandNZ F) fs] : Prog fs.ops D (D.sh F) := do
  let r ← randNZ F
  Prog.op (F := Invert F) ⟨(), (r, ())⟩

/-- The hybrid the caller is written in: silent inversion as a black box. -/
abbrev CallerHyb : Hybrid := [Invert F, RandNZ F]

/-- **The caller discharges the precondition**: every request it issues to
`Invert`, on the support of its ideal run, has a nonzero operand, because
the support of `RandNZ` is the nonzero elements. -/
theorem invertFresh_valid :
    Valid (CallerHyb F).model (fun r => match r with
        | ⟨⟨⟨0, _⟩, _⟩, a⟩ => a.1 ≠ 0
        | _ => True)
      (invertFresh F (fs := CallerHyb F) (D := .ideal)) := by
  refine .call _ _ trivial fun z hz => ?_
  refine .call _ _ ?_ fun _ _ => .pure _
  -- `z.1` is in the support of `uniform {t // t ≠ 0}` mapped to `F`
  have hz' : z ∈ ((RandNZ F).model.step ⟨.randNZ, ()⟩).support := hz
  rw [RandNZ.model_eq] at hz'
  simp only [RandNZ.model, PMF.support_map, PMF.support_uniformOfFintype, Set.mem_image] at hz'
  obtain ⟨t, -, rfl⟩ := hz'
  exact t.2

end

end Weft.Examples.Inversion
