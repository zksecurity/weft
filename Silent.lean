import Privacy

/-!
# Sanity check: with only `add` and `mul`, privacy is free

If no operation of the signature leaks, then *every* circuit over it
reveals nothing, and is therefore hiding with the trivial simulator.
Correctness of such a circuit is nothing but correctness of the arithmetic
it computes: `output` is by definition the evaluation of the circuit's
polynomial.
-/
namespace Glean

/-- No operation leaks. -/
def Model.Silent {σ : Sig} {L : Type} {m : Type → Type} (M : Model σ L m) : Prop :=
  ∀ {α : Type} (o : σ α) (x : α), M.leak o x = []

theorem Model.Silent.lift {σ : Sig} {L : Type} {m : Type → Type} [Monad m] {M : Model σ L Id} (h : M.Silent) :
    (M.lift m).Silent := h

section Eval
variable {σ : Sig} {L : Type} {M : Model σ L Id}

/-- Every run of every circuit over a silent model leaks nothing (evaluation). -/
theorem leak_nil_of_silent (hs : M.Silent) {α : Type} (c : Circ σ α) : leak M c = [] := by
  induction c with
  | pure a => rfl
  | call o k ih =>
    show M.leak o _ ++ leak M (k _) = []
    rw [hs, ih]
    rfl
end Eval

section Dist
variable {σ : Sig} {L C : Type} [AddMonoid C] {M : Model σ L PMF} {K : CostModel σ C}

/-- Every possible run over a silent model has empty leakage. -/
theorem leak_nil_of_silent_support (hs : M.Silent) {α : Type} (c : Circ σ α) :
    ∀ r ∈ (run M K c).support, r.2.leak = [] := by
  induction c with
  | pure a =>
    intro r hr
    simp only [run, PMF.monad_pure_eq_pure, PMF.support_pure, Set.mem_singleton_iff] at hr
    subst hr; rfl
  | call o k ih =>
    intro r hr
    simp only [run_call, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.support_bind, PMF.support_pure,
      Set.mem_iUnion, Set.mem_singleton_iff] at hr
    obtain ⟨x, _, r', hr', rfl⟩ := hr
    simp only [Trace.seq, List.append_eq_nil_iff]
    exact ⟨hs o x, ih x r' hr'⟩

/-- Two functions of a distribution that agree on its support give the same image. -/
theorem PMF.map_congr_support {α β : Type} {p : PMF α} {f g : α → β} (h : ∀ a ∈ p.support, f a = g a) :
    p.map f = p.map g := by
  ext b
  simp only [PMF.map_apply]
  refine tsum_congr fun a => ?_
  by_cases ha : a ∈ p.support
  · rw [h a ha]
  · simp [(PMF.apply_eq_zero_iff p a).2 ha]

/-- **Every circuit over a silent signature is hiding**, with the simulator
that outputs nothing. -/
theorem hiding_of_silent (hs : M.Silent) {I α : Type} (c : I → Circ σ α) : Hiding M c := by
  refine ⟨fun _ => pure [], fun i => ?_⟩
  simp only [dist, PMF.monad_map_eq_map, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.map_comp,
    PMF.bind_map, PMF.pure_bind]
  exact PMF.map_congr_support fun r hr => by simp [leak_nil_of_silent_support hs _ r hr]
end Dist

/-! ## The `add`/`mul` functionality is silent, so all its circuits are private -/

section
variable (F : Type) [Add F] [Mul F] [Sub F]
local notation "𝕀" => Domain.ideal F

abbrev Arith : Sig := Lin 𝕀 ⊞ Mult 𝕀
def Arith.ideal : Model (Arith F) F Id := (Lin.ideal F).sum (Mult.ideal F)

theorem Arith.silent : (Arith.ideal F).Silent := by
  intro α o x
  rcases o with o | o <;> cases o <;> rfl

/-- Any circuit over add and mul, hiding, with no proof about the circuit. -/
theorem Arith.hiding {I α : Type} (c : I → Circ (Arith F) α) : Hiding ((Arith.ideal F).lift PMF) c :=
  hiding_of_silent (Model.Silent.lift (Arith.silent F)) c

/-- And correctness is the arithmetic: `output` *is* the evaluation. -/
example (a b c : F) :
    output (Arith.ideal F) (Examples.mul3 (D := 𝕀) (σ := Arith F) a b c) = a * b * c := rfl
end

end Glean
