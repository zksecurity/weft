import Privacy
import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.FieldSimp

/-!
# Gadgets: circuits come with their specs

Clean's `FormalCircuit` bundles a circuit with `Assumptions`, a `Spec`, and
the proofs, so that a caller uses the spec and discharges the assumptions
without unfolding the callee.  The MPC version adds the one thing MPC
cares about: the *declared leakage*, what a caller's simulator may be
given, and the proof that the real reveals are simulatable from it.

Correctness is perfect: every output the circuit can produce satisfies the
spec.  A gadget that needs an invertible mask asks the functionality for a
nonzero one (`randNZ`); it does not gamble on the coins, so there is no set
of "good tapes" and nothing to count.  Privacy carries an explicit `ε`
(zero for perfect gadgets) measured as total variation, which is what adds
up under composition.

Price is *not* part of a gadget.  Semantics (program and leak) belongs to
the functionality and is the same on every MPC; price belongs to the MPC.
A gadget's cost on a given MPC is computed by running it against that
MPC's cost model (`Gadget.cost`), and a bound is a separate theorem about
the pair (gadget, cost model), not a field.
-/
namespace Glean

/-- A verified MPC gadget over the model `M` (the semantics of its signature). -/
structure Gadget {σ : Sig} {L : Type} (M : Model σ L PMF) (I O : Type) where
  /-- The circuit. -/
  circ : I → Circ σ O
  /-- What the caller must guarantee about the input. -/
  Assumptions : I → Prop
  /-- What the gadget guarantees about its output, under the assumptions. -/
  Spec : I → O → Prop
  /-- Declared leakage: what a simulator is given, as a function of input and output
  (like `Model.leak`, of request and response). -/
  view : I → O → List L
  /-- Perfect correctness: every output the circuit can produce satisfies the spec. -/
  correct : ∀ i, Assumptions i → ∀ o ∈ (Prod.fst <$> dist M (circ i)).support, Spec i o
  /-- Simulation error (total variation); `0` for perfect gadgets. -/
  ε : ENNReal := 0
  /-- The real (output, reveals) are within `ε` of (output, simulated reveals from the view). -/
  simulatable : ∃ Sim : List L → PMF (List L), ∀ i, Assumptions i →
    PMF.statDist (dist M (circ i))
      (do let y ← Prod.fst <$> dist M (circ i); let s ← Sim (view i y); pure (y, s)) ≤ ε

namespace Gadget
variable {σ : Sig} {L C I O : Type} {M : Model σ L PMF}

/-- A perfect gadget's obligation is an equation of distributions. -/
theorem perfect (circ : I → Circ σ O) (Assumptions : I → Prop) (view : I → O → List L)
    (Sim : List L → PMF (List L))
    (h : ∀ i, Assumptions i → dist M (circ i) =
      do let y ← Prod.fst <$> dist M (circ i); let s ← Sim (view i y); pure (y, s)) :
    ∃ Sim : List L → PMF (List L), ∀ i, Assumptions i →
      PMF.statDist (dist M (circ i))
        (do let y ← Prod.fst <$> dist M (circ i); let s ← Sim (view i y); pure (y, s)) ≤ 0 :=
  ⟨Sim, fun i hi => le_of_eq (PMF.statDist_eq_zero_of_eq (h i hi))⟩

/-- The cost of a gadget on an MPC is computed, for whatever cost model that
MPC has; a distribution in general, since a reactive circuit's shape may
depend on revealed values. -/
noncomputable def cost [AddMonoid C] (g : Gadget M I O) (K : CostModel σ C) (i : I) : PMF C :=
  (fun r => r.2.cost) <$> run M K (g.circ i)

/-- An optional, separate statement: on cost model `K`, the gadget costs
exactly `p` (for structurally scheduled gadgets, whatever the input). -/
def Priced [AddMonoid C] (g : Gadget M I O) (K : CostModel σ C) (p : C) : Prop :=
  ∀ i, g.cost K i = pure p

/-! ### A gadget is a functionality

A gadget with a deterministic spec function is one operation of a one-op
signature: `program := spec`, `leak := view`.  Callers use that; the
composition theorem (`Compose.lean`) makes their proofs sound for the
inlined circuit.  Sequential composition of gadgets is the special case of
a two-call caller, so it needs no primitive of its own. -/

/-- The one-op signature of a gadget. -/
inductive OpOf (I O : Type) : Sig where
  | call : I → OpOf I O O

/-- The abstract model of a gadget: what a caller is allowed to assume. -/
noncomputable def toModel (g : Gadget M I O) : Model (OpOf I O) L PMF where
  program o := match o with | .call i => Prod.fst <$> dist M (g.circ i)
  leak o x := match o with | .call i => g.view i x

/-- ...and the gadget's circuit realises it. -/
def impl (g : Gadget M I O) : {β : Type} → OpOf I O β → Circ σ β
  | _, .call i => g.circ i

/-- The gadget's obligation, restated as a realisation: the concrete *tagged*
view is simulatable from the declared one.  (`simulatable` above is the
untagged form, enough for a top-level `Hiding`; a gadget meant to be called
through its model proves this form, with the request kinds of `σ`.) -/
def RealizesModel {K : Type} (g : Gadget M I O) (kσ : {β : Type} → σ β → K) : Prop :=
  ∃ Sim : List L → PMF (List (K × List L)), ∀ i, g.Assumptions i →
    dist (M.tagged kσ) (g.circ i) = do
      let y ← Prod.fst <$> dist M (g.circ i)
      let s ← Sim (g.view i y)
      pure (y, s)

/-- A gadget whose assumptions always hold realises its own model. -/
theorem realizes {K : Type} (g : Gadget M I O) (kσ : {β : Type} → σ β → K)
    (h : g.RealizesModel kσ) (hA : ∀ i, g.Assumptions i) :
    Realizes kσ (fun _ => ()) g.impl M g.toModel := by
  obtain ⟨Sim, hSim⟩ := h
  refine ⟨fun _ => Sim, ?_⟩
  intro β o
  obtain ⟨i⟩ := o
  exact hSim i (hA i)
end Gadget

/-! ## Example: inversion by masking, with the assumption `x ≠ 0` -/

section
variable (F : Type) [Field F] [Fintype F] [DecidableEq F]
local notation "𝕀" => Domain.ideal F
abbrev InvSig (D : Domain) : Sig := Std D ⊞ RandNZ D
noncomputable def InvSig.ideal : Model (InvSig 𝕀) F PMF := ((Std.ideal F).lift PMF).sum (RandNZ.ideal F)

/-- `1/x = s / reveal(x·s)` for a nonzero mask `s`, polymorphic in the domain:
the same definition is run in the ideal domain for the gadget and in the
timed domain for delay. -/
def invert {D : Domain} [Inv D.F] (x : D.S) : Circ (InvSig D) D.S := do
  let s ← randNZ
  let v ← mul x s
  let m ← reveal v
  smul m⁻¹ s

/-- The semantics of `invert`. -/
theorem invert_dist (x : F) :
    dist (InvSig.ideal F) (invert (D := 𝕀) x)
      = (uniform {s : F // s ≠ 0}).bind fun s => pure ((x * s.1)⁻¹ * s.1, [x * s.1]) := by
  simp [dist, invert, InvSig.ideal, Model.sum, Lin.ideal, Mult.ideal, Reveal.ideal, RandNZ.ideal, Std.ideal,
    randNZ, mul, reveal, smul, Circ.op, Has.inj, run, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    PMF.monad_map_eq_map, PMF.map_bind, PMF.pure_map, PMF.bind_map, Function.comp_def, mul_comm]

/-- The gadget: needs `x ≠ 0`; then the output is `x⁻¹` with certainty and the
one revealed value `x·s` is a uniform nonzero element, simulatable from
nothing.  No price: that depends on the MPC. -/
noncomputable def invertGadget : Gadget (InvSig.ideal F) F F where
  circ := invert (D := 𝕀)
  Assumptions x := x ≠ 0
  Spec x y := y * x = 1
  view _ _ := []
  correct := by
    intro x hx y hy
    rw [invert_dist] at hy
    simp only [PMF.monad_map_eq_map, PMF.monad_pure_eq_pure, PMF.map_bind, PMF.pure_map, PMF.support_bind,
      PMF.support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hy
    obtain ⟨s, _, rfl⟩ := hy
    have := s.2
    field_simp
  simulatable := Gadget.perfect _ _ _ (fun _ => (uniform {t : F // t ≠ 0}).map fun t => [t.1]) fun x hx => by
    rw [invert_dist]
    -- the output is a point: `s / (x·s) = x⁻¹` on the whole support
    have out : ∀ s : {s : F // s ≠ 0}, (x * s.1)⁻¹ * s.1 = x⁻¹ := fun s => by
      have := s.2; field_simp
    simp only [out, PMF.monad_map_eq_map, PMF.monad_pure_eq_pure, PMF.monad_bind_eq_bind, PMF.map_bind,
      PMF.pure_map, PMF.bind_const, PMF.pure_bind, PMF.bind_map, Function.comp_def]
    -- the mask: `s ↦ x·s` is a bijection of the nonzero elements
    let e : {s : F // s ≠ 0} ≃ {t : F // t ≠ 0} :=
      (Equiv.mulLeft₀ x hx).subtypeEquiv fun s => by simp [hx]
    conv_rhs => rw [← uniform_map_equiv e, PMF.bind_map]
    rfl

-- Delay, separately, per MPC, on the polymorphic circuit in the timed domain:
-- two rounds where `mult` and `reveal` are one round each and `randNZ` is free...
local notation "𝕋" => Domain.timed F
def InvSig.timed [Inhabited F] (ℓrand : Nat) : Model (InvSig 𝕋) F Sched :=
  (Std.timed F).sum ⟨fun o => match o with | .randNZ => fun s => (⟨default, s.clock + ℓrand⟩, s), fun _ _ => []⟩
example [Inhabited F] (x : F) : delayOn (InvSig.timed F 0) (invert (D := 𝕋) ⟨x, 0⟩) = 2 := rfl
-- ...and three where `randNZ` costs a round (an MPC without PRSS).
example [Inhabited F] (x : F) : delayOn (InvSig.timed F 1) (invert (D := 𝕋) ⟨x, 0⟩) = 3 := rfl
-- Communication, as a `Priced` statement on the gadget: one multiplication and one reveal.
def InvSig.comm : CostModel (InvSig 𝕀) Nat :=
  ⟨fun o => match o with | .inl (.inr (.inl _)) => 2 | .inl (.inr (.inr _)) => 1 | _ => 0⟩
theorem invert_priced : (invertGadget F).Priced (InvSig.comm F) 3 := fun x => by
  simp [Gadget.cost, invertGadget, invert, InvSig.ideal, InvSig.comm, Model.sum, Lin.ideal, Mult.ideal,
    Reveal.ideal, RandNZ.ideal, Std.ideal, randNZ, mul, reveal, smul, Circ.op, Has.inj, run,
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.monad_map_eq_map, PMF.map_bind, PMF.pure_map,
    PMF.bind_map, PMF.bind_const, Function.comp_def, Trace.seq]
end

end Glean
