import Features
import Gallery
import Compose
import Functionality

/-!
# Rounds and communication, separately, and how they compose

Two resources, two families of theorems.  A price list carries both
numbers per feature, but nothing forces a theorem to mention both:
`delay` (the timed domain) and `comm` (an additive cost model) are
separate observables.

Composition ("universal composability for cost"): inlining an
implementation into a caller costs what the caller costs when each
abstract operation is priced at its implementation's cost.  For
communication this is exact (`cost_handle`).  For delay it is an
*upper bound* under dependency tracking, exact with timing profiles
(`Timing.lean`), because inlining exposes independence across operation
boundaries that the atomic view cannot see.
-/
namespace Glean

/-! ## Separate observables -/

/-- A price per operation. -/
abbrev Costs (σ : Sig) (C : Type) := {α : Type} → σ α → C

section
variable {σ : Sig} {L α : Type} (M : Model σ L Id)

/-- Communication under a per-operation bandwidth `b`, by evaluation.  (Delay
is not a `cost`: it is computed in the timed domain, `Glean.delay`.) -/
def comm (b : Costs σ Nat) (c : Circ σ α) : Nat := cost M ⟨b⟩ c
end

/-- The cost of a run, as a distribution (a reactive circuit's shape may depend
on what it reveals). -/
noncomputable def costDist {σ : Sig} {L C α : Type} [AddMonoid C] (M : Model σ L PMF) (K : CostModel σ C)
    (c : Circ σ α) : PMF C :=
  (fun r => r.2.cost) <$> run M K c

-- An MPC's price list gives both, separately.
namespace FS
variable {D : Domain} (M : MPC)

/-- Per-feature bandwidth; unsupported features never occur in a well-typed circuit, so `⊤` maps to 0. -/
def MPC.bandwidth : Costs (Ops D M) Nat := fun ⟨⟨f, _⟩, _⟩ => (M.cost f).elim 0 Price.comm

/-- Separate theorems about the same circuit on the same MPC: communication
by the additive cost model, delay by the timed model. -/
example (a b c : Int) :
    comm (honestMajority.eval Int) honestMajority.bandwidth (mulAdd (D := .ideal Int) a b c) = 2 := rfl
example (a b c : Int) :
    delayOn (honestMajority.timed Int) (mulAdd (D := .timed Int) ⟨a, 0⟩ ⟨b, 0⟩ ⟨c, 0⟩) = 1 := rfl

-- Delay does not stack across independent work; communication does.
example (a b : Int) :
    comm (honestMajority.eval Int) honestMajority.bandwidth (fourPar (D := .ideal Int) a b) = 8 := rfl
example (a b : Int) :
    comm (honestMajority.eval Int) honestMajority.bandwidth (fourSeq (D := .ideal Int) a b) = 8 := rfl
example (a b : Int) :
    delayOn (honestMajority.timed Int) (fourSeq (D := .timed Int) ⟨a, 0⟩ ⟨b, 0⟩) = 4 := rfl
end FS

/-! ## Composition theorems for cost -/

/-- Two continuations that agree on the support of `p` give the same bind. -/
theorem PMF.bind_congr_support {α β : Type} {p : PMF α} {f g : α → PMF β} (h : ∀ a ∈ p.support, f a = g a) :
    p.bind f = p.bind g := by
  ext b
  simp only [PMF.bind_apply]
  refine tsum_congr fun a => ?_
  by_cases ha : a ∈ p.support
  · rw [h a ha]
  · simp [(PMF.apply_eq_zero_iff p a).2 ha]

section
variable {σ τ : Sig} {L : Type}

/-- An implementation is *priced* under `K` if each operation's circuit has
a cost independent of its arguments and coins (structurally scheduled). -/
def PricedImpl {C : Type} [AddMonoid C] (Mσ : Model σ L PMF) (impl : {β : Type} → τ β → Circ σ β)
    (K : CostModel σ C) (p : Costs τ C) : Prop :=
  ∀ {β : Type} (o : τ β), costDist Mσ K (impl o) = pure (p o)

/-- **Composition, communication.**  Inlining a priced implementation into a
caller costs what the caller costs with each abstract operation priced at
its implementation's cost. -/
theorem cost_handle {C Kσ Kτ α : Type} [AddMonoid C] {Mσ : Model σ L PMF} {Mτ : Model τ L PMF}
    {kσ : {β : Type} → σ β → Kσ} {kτ : {β : Type} → τ β → Kτ}
    {impl : {β : Type} → τ β → Circ σ β} {K : CostModel σ C} {p : Costs τ C}
    (h : Realizes kσ kτ impl Mσ Mτ) (hp : PricedImpl Mσ impl K p) (P : Circ τ α) :
    costDist Mσ K (Circ.handle impl P) = costDist Mτ ⟨p⟩ P := by
  obtain ⟨Sim, hSim⟩ := h
  induction P with
  | pure a => simp [Circ.handle, costDist, run]
  | call o k ih =>
    -- the implementation's result is distributed as the abstract program's
    have fst : Prod.fst <$> run Mσ K (impl o) = Mτ.program o := by
      rw [run_fst Mσ (Mσ.tagged kσ) (fun _ => rfl) K CostModel.unit]
      have := congrArg (fun d => Prod.fst <$> d) (hSim o)
      simpa [dist, PMF.monad_map_eq_map, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.map,
        Function.comp_def, PMF.bind_bind, PMF.pure_bind, PMF.bind_const, PMF.bind_pure] using this
    -- ...and its cost is `p o` on the whole support
    have cst : ∀ r ∈ (run Mσ K (impl o)).support, r.2.cost = p o := by
      intro r hr
      have := hp o
      simp only [costDist, PMF.monad_map_eq_map, PMF.monad_pure_eq_pure] at this
      have := congrArg PMF.support this
      rw [PMF.support_map, PMF.support_pure] at this
      have : r.2.cost ∈ (fun r : _ × Trace C L => r.2.cost) '' (run Mσ K (impl o)).support := ⟨r, hr, rfl⟩
      simpa [*] using this
    rw [Circ.handle, costDist, run_bind]
    simp only [costDist, run_call, PMF.monad_map_eq_map, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
      PMF.map_bind, PMF.pure_map] at ih ⊢
    rw [PMF.bind_congr_support (g := fun r => (run Mσ K (Circ.handle impl (k r.1))).bind fun s =>
      PMF.pure (p o + s.2.cost)) (fun r hr => by simp [Trace.seq, cst r hr])]
    have e : ((run Mσ K (impl o)).bind fun r => (run Mσ K (Circ.handle impl (k r.1))).bind fun s =>
        PMF.pure (p o + s.2.cost)) = (Prod.fst <$> run Mσ K (impl o)).bind fun y =>
          (run Mσ K (Circ.handle impl (k y))).bind fun s => PMF.pure (p o + s.2.cost) := by
      simp [PMF.monad_map_eq_map, PMF.bind_map, Function.comp_def]
    rw [e, fst]
    congr 1
    funext y
    have := ih y
    calc ((run Mσ K (Circ.handle impl (k y))).bind fun s => PMF.pure (p o + s.2.cost))
        = ((run Mσ K (Circ.handle impl (k y))).map fun s => s.2.cost).bind fun c => PMF.pure (p o + c) := by
          simp [PMF.bind_map, Function.comp_def]
      _ = ((run Mτ ⟨p⟩ (k y)).map fun s => s.2.cost).bind fun c => PMF.pure (p o + c) := by rw [this]
      _ = _ := by simp [PMF.bind_map, Function.comp_def, Trace.seq]

/-- Communication composes exactly. -/
theorem comm_handle {Kσ Kτ α : Type} {Mσ : Model σ L PMF} {Mτ : Model τ L PMF}
    {kσ : {β : Type} → σ β → Kσ} {kτ : {β : Type} → τ β → Kτ}
    {impl : {β : Type} → τ β → Circ σ β} {b : Costs σ Nat} {bτ : Costs τ Nat}
    (h : Realizes kσ kτ impl Mσ Mτ) (hp : PricedImpl Mσ impl ⟨b⟩ bτ) (P : Circ τ α) :
    costDist Mσ ⟨b⟩ (Circ.handle impl P) = costDist Mτ ⟨bτ⟩ P :=
  cost_handle h hp P

-- Delay composes exactly as well, in the timed domain, once an abstract
-- operation is modelled by its *timing profile* (delay from each input to
-- the output) rather than a single latency; see `Timing.lean`.  The theorem
-- is the decomposition of the longest path through a substituted dependency
-- graph at the substitution boundary; stated there, proof deferred.
end

/-! ## At the level of functionalities: derived prices compose -/

/-- The price a realisation gives to each operation of `F` on `G`'s cost model. -/
noncomputable def Realization.derivedPrice {L C : Type} [AddMonoid C] {F G : Functionality L}
    (r : Realization F G) (K : CostModel G.ops C) : {β : Type} → F.ops β → PMF C :=
  fun o => costDist G.model K (r.impl o)

/-- Derived prices compose along `Realization.comp`, one `cost_handle` per level. -/
theorem Realization.comp_derivedPrice {L C : Type} [AddMonoid C] {F G H : Functionality L}
    (f : Realization F G) (g : Realization G H) (K : CostModel H.ops C) {p : Costs G.ops C}
    (hp : PricedImpl H.model g.impl K p) {β : Type} (o : F.ops β) :
    (f.comp g).derivedPrice K o = costDist G.model ⟨p⟩ (f.impl o) :=
  cost_handle g.realizes hp (f.impl o)

end Glean
