import Weft
import Examples.Basic
import Examples.Beaver

/-!
# Privacy: one certificate, and what it composes to

Every privacy statement is a realisation of a functionality.  This file
shows the shapes:

* **The black box over the preprocessing box.**  Beaver multiplication
  realises `Mult`; linear operations and reveal realise themselves (the
  trusted base); together they are realisations of every component of
  `Std F` over `Pre F`, and *every* program over the black box transports,
  with no new proof.
* **A program as a one-operation functionality.**  "`openMul` reveals
  nothing beyond its output" is: `openMul` realises the functionality that
  returns `a·b` in the clear.  The simulator is handed the event, whose
  clear output is `a·b`, and replays the two records.
* **Two non-examples**, the ones the old definitions got wrong (report,
  Issues 1 and 3): opening an input and returning it is not a realisation
  of the identity functionality, because the event blanks a share output
  while the view shows the value; and revealing both inputs is not a
  realisation of `OpenMul`, because two inputs with the same output have
  different views.
* **Composition**: the one-operation certificate over the black box,
  composed with the black box over the preprocessing box, is a certificate
  over the preprocessing box.
-/
namespace Weft.Examples.Privacy
open Weft.Examples.Basic Weft.Examples.Beaver

section
variable (F : Type) [Field F] [Fintype F] [Inhabited F]

/-! ## The black box over the preprocessing box -/

/-- Every component of `Std F`, realised over `Pre F`: linear operations
and reveal by themselves, multiplication by Beaver. -/
noncomputable def stdOverPre : Realizations (Std F) (Pre F) :=
  .cons (Realization.incl (Lin F) (Pre F)) (.cons (beaverMult F) (.cons (Realization.incl (Reveal F) (Pre F)) .nil))

/-- **Every program over the black box transports.**  Its concrete run over
the preprocessing box is its abstract run with each event simulated: the
multiplication events become Beaver views with fresh uniform openings. -/
theorem transport_std_pre {α : Type} (c : Prog (Std F).ops .ideal α) :
    dist (Pre F).model (Prog.handle ((stdOverPre F).impl .ideal) c) = (do
      let r ← dist (Std F).model c
      let s ← simList (stdOverPre F).Sim r.2
      pure (r.1, s)) :=
  handle_realizes (stdOverPre F) c (Valid.of_forall _ (fun r => by
    obtain ⟨⟨⟨_ | _ | _ | n, h⟩, o⟩, a⟩ := r <;> trivial) c)

/-- And correctness transports: the output distribution is unchanged. -/
theorem output_std_pre {α : Type} (c : Prog (Std F).ops .ideal α) :
    Prod.fst <$> dist (Pre F).model (Prog.handle ((stdOverPre F).impl .ideal) c) = Prod.fst <$> dist (Std F).model c :=
  output_transport (stdOverPre F) c (Valid.of_forall _ (fun r => by
    obtain ⟨⟨⟨_ | _ | _ | n, h⟩, o⟩, a⟩ := r <;> trivial) c)

/-! ## A program as a one-operation functionality -/

/-- The functionality "multiply and publish the product": one operation on
two share operands, a clear response, nothing further declared. -/
abbrev OpenMul : Functionality :=
  .ofEval ⟨Unit, fun _ => .share F ⊗ .share F, fun _ => .clear F, fun _ => Unit⟩
    ⟨fun r => pure (r.args.1 * r.args.2, ())⟩

/-- **`openMul` reveals nothing beyond its output.**  The simulator sees the
event `((), a·b, ())` and replays the multiplication record and the reveal
of `a·b`. -/
program openMulReal : Realization (OpenMul F) (Std F) where
  impl D r := openMul r.args.1 r.args.2
  Sim e := pure [⟨Std.mult F, ((), ()), (), ()⟩, ⟨Std.reveal F, (), e.out, ()⟩]
  real r _ := by
    obtain ⟨⟨⟩, a, b⟩ := r
    simp only [openMul, mul, reveal, weft, Functionality.ofEval_model]
    rfl

omit [Fintype F] [Inhabited F] in
/-- **Not private: revealing both inputs.**  The inputs `(0, 1)` and `(1, 0)`
have the same output `0`, hence the same event, so one simulator output
would have to be both views. -/
theorem leakyMul_not_realizes :
    ¬ ∃ Sim : Event (OpenMul F).ops → PMF (List (Event (Std F).ops)),
      ∀ a b : F, dist (Std F).model (leakyMul (fs := Std F) (D := .ideal) a b) = (do
        let p ← (OpenMul F).model.step ⟨(), (a, b)⟩
        let s ← Sim ⟨(), ((), ()), p.1, p.2⟩
        pure (p.1, s)) := by
  rintro ⟨Sim, h⟩
  have h₁ := h 0 1
  have h₂ := h 1 0
  simp only [leakyMul, reveal, weft, Functionality.ofEval_model, zero_mul, mul_zero] at h₁ h₂
  -- both runs are points with the same simulated side, so they are the same point
  have same := congrArg PMF.support (h₁.trans h₂.symm)
  simp only [PMF.support_pure, Set.singleton_eq_singleton_iff, Prod.mk.injEq, List.cons.injEq,
    Event.mk.injEq, heq_eq_eq, true_and] at same
  exact one_ne_zero same.2.1.1

/-- The functionality "return the share you were given": one share operand,
one share response, nothing declared. -/
abbrev Keep : Functionality :=
  .ofEval ⟨Unit, fun _ => .share F, fun _ => .share F, fun _ => Unit⟩
    ⟨fun r => pure (r.args, ())⟩

/-- Open the secret, then return the same share.  With the old definition,
which handed the simulator the output, this was "hiding" at the ideal
domain (report, Issue 1). -/
def openKeep {fs : Hybrid} {D : Domain} [Has (Reveal F) fs] (x : D.share F) : Prog fs.ops D (D.share F) := do
  let _ ← reveal x
  pure x

omit [Fintype F] [Inhabited F] in
/-- **Not private: `openKeep` does not realise `Keep`.**  The event blanks
the share output, so it is the same for every input, while the view shows
the value opened. -/
theorem openKeep_not_realizes :
    ¬ ∃ Sim : Event (Keep F).ops → PMF (List (Event (Std F).ops)),
      ∀ x : F, dist (Std F).model (openKeep F (fs := Std F) (D := .ideal) x) = (do
        let p ← (Keep F).model.step ⟨(), x⟩
        let s ← Sim ⟨(), (), (), p.2⟩
        pure (p.1, s)) := by
  rintro ⟨Sim, h⟩
  have h₀ := h 0
  have h₁ := h 1
  simp only [openKeep, reveal, weft, Functionality.ofEval_model] at h₀ h₁
  -- the view marginals: `Sim ((), (), ())` is a point at `[reveal 0]` and at `[reveal 1]`
  have s₀ := congrArg (PMF.map Prod.snd) h₀
  have s₁ := congrArg (PMF.map Prod.snd) h₁
  simp only [PMF.map_bind, PMF.pure_map, PMF.bind_pure] at s₀ s₁
  have same := congrArg PMF.support (s₀.trans s₁.symm)
  simp only [PMF.support_pure, Set.singleton_eq_singleton_iff, List.cons.injEq, Event.mk.injEq, heq_eq_eq,
    true_and] at same
  exact zero_ne_one same.1.1

/-! ## Composition: the certificate over the preprocessing box, for free -/

/-- `openMul` over `Pre F`, by composition.  No new simulator, no new proof. -/
noncomputable def openMulOverPre : Realization (OpenMul F) (Pre F) :=
  (openMulReal F).comp (stdOverPre F)

-- The composed implementation is Beaver multiplication then a reveal, literally.
example (a b : F) :
    (openMulOverPre F).impl .ideal ⟨(), (a, b)⟩
      = Prog.handle ((stdOverPre F).impl .ideal) (openMul (fs := Std F) (D := .ideal) a b) := rfl
end

end Weft.Examples.Privacy
