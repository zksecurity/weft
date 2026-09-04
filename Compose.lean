import Privacy
import Gadget

/-!
# Privacy of composed circuits: a verified circuit is a functionality

A primitive operation has a `program` (what it returns) and a `leak` (what
the adversary sees).  A *verified circuit* gets the same two things:

* its `program` is its spec (what it computes on the ideal functionality);
* its `leak` is its *declared* leakage, the `view` of its gadget.

Callers then treat the circuit as one more operation of an abstract
signature and prove their own privacy against that abstract model.  The
theorem below says those proofs are sound for the concrete circuit with
the callee inlined: if every abstract operation is *realised* by a circuit
whose concrete view is simulatable from the declared record, then any
caller's concrete run is simulatable from its abstract run.  This is the
UC composition theorem at the level of this semantics, proved by
induction over the caller's free-monad trace using only `run_bind`.
-/
namespace Glean

/-- Run the per-record simulators along an abstract trace. -/
noncomputable def simList {L Kσ Kτ : Type} (Sim : Kτ → List L → PMF (List (Kσ × List L))) :
    List (Kτ × List L) → PMF (List (Kσ × List L))
  | [] => pure []
  | r :: rs => do
    let s ← Sim r.1 r.2
    let t ← simList Sim rs
    pure (s ++ t)

/-- **Composition.**  If `impl` realises `Mτ` on `Mσ` with simulators `Sim`,
then for any caller `c` the concrete run of `handle impl c` is the abstract
run of `c` with each declared record replaced by its simulation. -/
theorem handle_realizes {σ τ : Sig} {L Kσ Kτ α : Type}
    {kσ : {β : Type} → σ β → Kσ} {kτ : {β : Type} → τ β → Kτ}
    {impl : {β : Type} → τ β → Circ σ β} {Mσ : Model σ L PMF} {Mτ : Model τ L PMF}
    (Sim : Kτ → List L → PMF (List (Kσ × List L)))
    (h : ∀ {β : Type} (o : τ β), dist (Mσ.tagged kσ) (impl o) =
      do let y ← Mτ.program o; let s ← Sim (kτ o) (Mτ.leak o y); pure (y, s))
    (c : Circ τ α) :
    dist (Mσ.tagged kσ) (Circ.handle impl c) = (do
      let r ← dist (Mτ.tagged kτ) c
      let s ← simList Sim r.2
      pure (r.1, s)) := by
  induction c with
  | pure a => simp [Circ.handle, dist, simList]
  | call o k ih =>
    rw [Circ.handle, dist_bind, h o]
    simp only [ih, dist_call, Model.tagged_program, Model.tagged_leak, List.singleton_append, simList,
      bind_assoc, pure_bind, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.monad_map_eq_map, PMF.map_bind,
      PMF.pure_map, PMF.bind_bind, PMF.pure_bind]
    congr 1
    funext x
    -- the simulator's coins for this call are independent of the rest of the run
    rw [PMF.bind_comm]

/-- Realisations compose: inlining a realisation of `τ` over `σ` into a
realisation of `ρ` over `τ` realises `ρ` over `σ`. -/
theorem Realizes.comp {σ τ ρ : Sig} {L Kσ Kτ Kρ : Type}
    {kσ : {β : Type} → σ β → Kσ} {kτ : {β : Type} → τ β → Kτ} {kρ : {β : Type} → ρ β → Kρ}
    {f : {β : Type} → ρ β → Circ τ β} {g : {β : Type} → τ β → Circ σ β}
    {Mσ : Model σ L PMF} {Mτ : Model τ L PMF} {Mρ : Model ρ L PMF}
    (hf : Realizes kτ kρ f Mτ Mρ) (hg : Realizes kσ kτ g Mσ Mτ) :
    Realizes kσ kρ (fun o => Circ.handle g (f o)) Mσ Mρ := by
  obtain ⟨SimF, hF⟩ := hf
  obtain ⟨SimG, hG⟩ := hg
  refine ⟨fun k l => do let r ← SimF k l; simList SimG r, ?_⟩
  intro β o
  rw [handle_realizes SimG hG (f o), hF o]
  simp

/-- The trusted realisation: calling the operation itself. -/
theorem Realizes.id {σ : Sig} {L K : Type} (k : {β : Type} → σ β → K) (M : Model σ L PMF) :
    Realizes k k (fun o => Circ.op o) M M := by
  refine ⟨fun k l => pure [(k, l)], ?_⟩
  intro β o
  simp [dist, Circ.op, Has.inj, Model.tagged, run, Trace.seq]

/-- The payoff: hiding proved against the abstract functionality holds for
the concrete circuit, with no new proof. -/
theorem Hiding.transport {σ τ : Sig} {L Kσ Kτ I α : Type}
    {kσ : {β : Type} → σ β → Kσ} {kτ : {β : Type} → τ β → Kτ}
    {impl : {β : Type} → τ β → Circ σ β} {Mσ : Model σ L PMF} {Mτ : Model τ L PMF}
    (h : Realizes kσ kτ impl Mσ Mτ) (P : I → Circ τ α) (hP : Hiding (Mτ.tagged kτ) P) :
    Hiding (Mσ.tagged kσ) (fun i => Circ.handle impl (P i)) := by
  obtain ⟨Sim, hSim⟩ := h
  obtain ⟨SimP, hP⟩ := hP
  refine ⟨fun y => do let r ← SimP y; simList Sim r, fun i => ?_⟩
  have e := handle_realizes Sim hSim (P i)
  -- the output distribution is unchanged by inlining
  have out : Prod.fst <$> dist (Mσ.tagged kσ) (Circ.handle impl (P i))
      = Prod.fst <$> dist (Mτ.tagged kτ) (P i) := by
    rw [e]
    simp [PMF.monad_bind_eq_bind, PMF.monad_map_eq_map, PMF.monad_pure_eq_pure, PMF.map, Function.comp_def,
      PMF.bind_const]
  rw [out, e]
  conv_lhs => rw [hP i]
  simp [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.monad_map_eq_map, PMF.map_bind, PMF.pure_map,
    PMF.bind_bind, PMF.pure_bind, Function.comp_def]

/-- The result of a run does not depend on the cost model or on what is leaked. -/
theorem run_fst {σ : Sig} {C C' L L' α : Type} [AddMonoid C] [AddMonoid C'] {m : Type → Type} [Monad m]
    [LawfulMonad m] (M : Model σ L m) (M' : Model σ L' m)
    (hp : ∀ {β : Type} (o : σ β), M.program o = M'.program o) (K : CostModel σ C) (K' : CostModel σ C')
    (c : Circ σ α) : Prod.fst <$> run M K c = Prod.fst <$> run M' K' c := by
  induction c with
  | pure a => simp [run]
  | call o k ih => simp [run_call, hp, ih]

/-- The output distribution does not depend on what is leaked. -/
theorem dist_fst_tagged {σ : Sig} {L K α : Type} (M : Model σ L PMF) (k : {β : Type} → σ β → K) (c : Circ σ α) :
    Prod.fst <$> dist M c = Prod.fst <$> dist (M.tagged k) c := by
  simp only [dist, Functor.map_map]
  exact run_fst M (M.tagged k) (fun _ => rfl) _ _ c

/-- Correctness transports too: the output distribution of the inlined
circuit is that of the caller on the abstract functionality. -/
theorem output_transport {σ τ : Sig} {L Kσ Kτ α : Type}
    {kσ : {β : Type} → σ β → Kσ} {kτ : {β : Type} → τ β → Kτ}
    {impl : {β : Type} → τ β → Circ σ β} {Mσ : Model σ L PMF} {Mτ : Model τ L PMF}
    (h : Realizes kσ kτ impl Mσ Mτ) (c : Circ τ α) :
    Prod.fst <$> dist Mσ (Circ.handle impl c) = Prod.fst <$> dist Mτ c := by
  obtain ⟨Sim, hSim⟩ := h
  rw [dist_fst_tagged Mσ kσ, handle_realizes Sim hSim c, dist_fst_tagged Mτ kτ]
  simp [PMF.monad_bind_eq_bind, PMF.monad_map_eq_map, PMF.monad_pure_eq_pure, PMF.map, Function.comp_def,
    PMF.bind_const]

/-! ## Example: Beaver multiplication realises `Mult`, and every `Std` proof transports -/

section
variable (F : Type) [Field F] [Fintype F]
local notation "𝕀" => Domain.ideal F

/-- Every circuit proved hiding on `Std` is hiding on `Pre` after inlining
Beaver multiplication, with no new proof. -/
example (I : Type) (P : I → Circ (Std 𝕀) F)
    (hP : Hiding (((Std.ideal F).lift PMF).tagged Std.kind) P) :
    Hiding ((Pre.ideal F).tagged Pre.kind) (fun i => Circ.handle (preHandler F) (P i)) :=
  Hiding.transport (preHandler_realizes F) P hP
end

end Glean
