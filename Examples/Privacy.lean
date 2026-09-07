import Weft
import Examples.Basic
import Examples.Beaver

/-!
# Privacy and composition

`stdOverPre` implements standard arithmetic using Beaver preprocessing.
The transport theorems preserve a caller's output distribution,
with each abstract event replaced by its simulation.

`openMulReal` specifies multiplication followed by public output.
Its simulator receives the product and reconstructs the two events.
Composing with `stdOverPre` gives the corresponding realisation over `Pre F`.

Two counterexamples show why the simulator receives an event:
revealing both operands discloses more than their product,
and revealing a share discloses more than returning it as a share.
-/
namespace Weft.Examples.Privacy
open Weft.Examples.Basic Weft.Examples.Beaver

section
variable (F : Type) [Field F] [Fintype F] [Inhabited F]

/-! ## Standard arithmetic from preprocessing -/

/-- Realise multiplication by Beaver and the remaining components by inclusion. -/
noncomputable def stdOverPre : Realizations (Std F) (Pre F) :=
  .cons (Realization.incl (Lin F) (Pre F)) (.cons (beaverMult F) (.cons (Realization.incl (Reveal F) (Pre F)) .nil))

/-- Replace each event of `Std F` with its preprocessing simulation. -/
theorem transport_std_pre {α : Type} (c : Prog (Std F).ops .ideal α) :
    dist (Pre F).model (Prog.handle ((stdOverPre F).impl .ideal) c) = (do
      let r ← dist (Std F).model c
      let s ← simList (stdOverPre F).Sim r.2
      pure (r.1, s)) :=
  handle_realizes (stdOverPre F) c (Valid.of_forall _ (fun r => by
    obtain ⟨⟨⟨_ | _ | _ | n, h⟩, o⟩, a⟩ := r <;> trivial) c)

/-- The preprocessing implementation preserves the output distribution. -/
theorem output_std_pre {α : Type} (c : Prog (Std F).ops .ideal α) :
    Prod.fst <$> dist (Pre F).model (Prog.handle ((stdOverPre F).impl .ideal) c) = Prod.fst <$> dist (Std F).model c :=
  output_transport (stdOverPre F) c (Valid.of_forall _ (fun r => by
    obtain ⟨⟨⟨_ | _ | _ | n, h⟩, o⟩, a⟩ := r <;> trivial) c)

/-! ## Public multiplication output -/

/-- Multiply two shared operands and return the product in the clear. -/
abbrev OpenMul : Functionality :=
  .ofEval ⟨Unit, fun _ => [.share F, .share F], fun _ => .clear F, fun _ => Unit⟩
    ⟨fun r => pure (r.args.1 * r.args.2.1, ())⟩

/-- Simulate `openMul` using the product in the ideal event. -/
program openMulReal : Realization (OpenMul F) (Std F) where
  impl D r := openMul r.args.1 r.args.2.1
  Sim e := pure [⟨Std.mult F, ((), (), ()), (), ()⟩, ⟨Std.reveal F, ((), ()), e.out, ()⟩]
  real r _ := by
    obtain ⟨⟨⟩, a, b, ⟨⟩⟩ := r
    simp only [openMul, mul, reveal, weft, Functionality.ofEval_model]
    rfl

omit [Fintype F] [Inhabited F] in
/-- Inputs `(0, 1)` and `(1, 0)` have the same product but different revealed operands.
Hence their views cannot share a simulator for the `OpenMul` event. -/
theorem leakyMul_not_realizes :
    ¬ ∃ Sim : Event (OpenMul F).ops → PMF (List (Event (Std F).ops)),
      ∀ a b : F, dist (Std F).model (leakyMul (fs := Std F) (D := .ideal) a b) = (do
        let p ← (OpenMul F).model.step ⟨(), (a, b, ())⟩
        let s ← Sim ⟨(), ((), (), ()), p.1, p.2⟩
        pure (p.1, s)) := by
  rintro ⟨Sim, h⟩
  have h₁ := h 0 1
  have h₂ := h 1 0
  simp only [leakyMul, reveal, weft, Functionality.ofEval_model, zero_mul, mul_zero] at h₁ h₂
  -- Both runs equal the same simulated distribution, so their supports must agree.
  have same := congrArg PMF.support (h₁.trans h₂.symm)
  simp only [PMF.support_pure, Set.singleton_eq_singleton_iff, Prod.mk.injEq, List.cons.injEq,
    Event.mk.injEq, heq_eq_eq, true_and] at same
  exact one_ne_zero same.2.1.1

/-- Return the input share without disclosure. -/
abbrev Keep : Functionality :=
  .ofEval ⟨Unit, fun _ => [.share F], fun _ => .share F, fun _ => Unit⟩
    ⟨fun r => pure (r.args.1, ())⟩

/-- Reveal the input, then return its original share. -/
def openKeep {fs : Hybrid} {D : Domain} [Has (Reveal F) fs] (x : D.share F) : Prog fs.ops D (D.share F) := do
  let _ ← reveal x
  pure x

omit [Fintype F] [Inhabited F] in
/-- `Keep` has the same event for every input,
while `openKeep` reveals the input value. -/
theorem openKeep_not_realizes :
    ¬ ∃ Sim : Event (Keep F).ops → PMF (List (Event (Std F).ops)),
      ∀ x : F, dist (Std F).model (openKeep F (fs := Std F) (D := .ideal) x) = (do
        let p ← (Keep F).model.step ⟨(), (x, ())⟩
        let s ← Sim ⟨(), ((), ()), (), p.2⟩
        pure (p.1, s)) := by
  rintro ⟨Sim, h⟩
  have h₀ := h 0
  have h₁ := h 1
  simp only [openKeep, reveal, weft, Functionality.ofEval_model] at h₀ h₁
  -- The same simulated view would have to reveal both zero and one.
  have s₀ := congrArg (PMF.map Prod.snd) h₀
  have s₁ := congrArg (PMF.map Prod.snd) h₁
  simp only [PMF.map_bind, PMF.pure_map, PMF.bind_pure] at s₀ s₁
  have same := congrArg PMF.support (s₀.trans s₁.symm)
  simp only [PMF.support_pure, Set.singleton_eq_singleton_iff, List.cons.injEq, Event.mk.injEq, heq_eq_eq,
    true_and] at same
  exact zero_ne_one same.1.1

/-! ## Composition over preprocessing -/

/-- Compose `openMulReal` with the preprocessing realisations. -/
noncomputable def openMulOverPre : Realization (OpenMul F) (Pre F) :=
  (openMulReal F).comp (stdOverPre F)

-- Unfolding the composition gives Beaver multiplication followed by reveal.
example (a b : F) :
    (openMulOverPre F).impl .ideal ⟨(), (a, b, ())⟩
      = Prog.handle ((stdOverPre F).impl .ideal) (openMul (fs := Std F) (D := .ideal) a b) := rfl
end

end Weft.Examples.Privacy
