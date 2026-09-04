import Glean
import MultiField
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Privacy: simulation on the distribution semantics

Everything an adversary can see of a circuit run over an ideal
functionality is what the functionality *leaks*: revealed values, public
coins, whatever an operation declares.  Everything else (honest inputs,
masks, the values inside shares) is hidden by fiat: we never model the MPC
protocol.  Privacy statements are all of one shape:

    "X can be simulated given Y"

meaning the joint distribution of `(Y, X)` equals that of `(Y, Sim Y)` with
the simulator's coins fresh.  The semantics is Mathlib's `PMF`, so this is
literally an equation between distributions.  There is no tape: each coin
is a fresh `bind` of a uniform distribution, so any number of coins drawn by
a run are *jointly* uniform (`seqUniform_eq_uniform` below), which is what
every mask argument needs and what a coordinate-wise statement would not
give.  The proof rule for masks is the lemma `uniform_map_equiv` (core §5).
-/
namespace Glean

/-! ## Notation for shares -/

/-- `⟦F⟧` is the type of a share of an `F` (the field-generic domain). -/
scoped notation "⟦" F "⟧" => Glean.MF.Domain.S _ F

/-! ## Fresh coins are jointly uniform

`k` sequential draws are one draw from `F^k`.  This is a theorem about
`bind`, not a modelling assumption, and it is the reason there is no tape:
a tape would have to *assume* it. -/

section Joint
variable {α β : Type} [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]

/-- Two fresh draws are one draw from the product. -/
theorem uniform_prod :
    (do let a ← PMF.uniformOfFintype α; let b ← PMF.uniformOfFintype β; pure (a, b))
      = PMF.uniformOfFintype (α × β) := by
  ext ⟨a, b⟩
  simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_apply, PMF.uniformOfFintype_apply,
    PMF.pure_apply, Prod.mk.injEq]
  rw [tsum_eq_single a, tsum_eq_single b]
  · simp [Fintype.card_prod, ENNReal.mul_inv]
  · intro b' hb; simp [Ne.symm hb]
  · intro a' ha; simp [Ne.symm ha]

/-- `n` fresh draws in sequence. -/
noncomputable def seqUniform (F : Type) [Fintype F] [Nonempty F] : (n : Nat) → PMF (Fin n → F)
  | 0 => pure fun i => i.elim0
  | n + 1 => do
    let x ← PMF.uniformOfFintype F
    let xs ← seqUniform F n
    pure (Fin.cons x xs)

/-- **Joint uniformity.**  `n` fresh draws are jointly uniform on `F^n`. -/
theorem seqUniform_eq_uniform (F : Type) [Fintype F] [Nonempty F] :
    ∀ n, seqUniform F n = PMF.uniformOfFintype (Fin n → F)
  | 0 => by
    ext v
    simp only [seqUniform, PMF.monad_pure_eq_pure, PMF.pure_apply, PMF.uniformOfFintype_apply]
    have : v = fun i => i.elim0 := funext fun i => i.elim0
    simp [this]
  | n + 1 => by
    have h : seqUniform F (n + 1) =
        ((do let a ← PMF.uniformOfFintype F; let b ← PMF.uniformOfFintype (Fin n → F); pure (a, b)) :
          PMF (F × (Fin n → F))).map fun p => Fin.cons p.1 p.2 := by
      simp only [seqUniform, seqUniform_eq_uniform F n, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
        PMF.map_bind, PMF.pure_map]
    rw [h, uniform_prod]
    exact uniform_map_equiv (Fin.consEquiv fun _ => F)
end Joint

/-! ## The adversary's view: the tagged trace

What the adversary observes of a run is, per request, *which* operation
was invoked (the program is public; the request's public kind) and what
the functionality declares for it.  `Model.tagged` records exactly that,
one record per request; `dist` of the tagged model is the distribution of
(output, view).  Simulators are applied per record, which is what makes
realisations compose. -/

/-- The model that leaks one `(kind, declared leak)` record per request. -/
def Model.tagged {τ : Sig} {L K : Type} {m : Type → Type} (Mτ : Model τ L m) (kind : {β : Type} → τ β → K) :
    Model τ (K × List L) m where
  program := Mτ.program
  leak o y := [(kind o, Mτ.leak o y)]

@[simp] theorem Model.tagged_program {τ : Sig} {L K : Type} {m : Type → Type} (Mτ : Model τ L m)
    (kind : {β : Type} → τ β → K) {β : Type} (o : τ β) : (Mτ.tagged kind).program o = Mτ.program o := rfl
@[simp] theorem Model.tagged_leak {τ : Sig} {L K : Type} {m : Type → Type} (Mτ : Model τ L m)
    (kind : {β : Type} → τ β → K) {β : Type} (o : τ β) (y : β) :
    (Mτ.tagged kind).leak o y = [(kind o, Mτ.leak o y)] := rfl

/-- A deterministic model's tagged view is the lift of its tagged view. -/
theorem Model.tagged_lift {τ : Sig} {L K : Type} (M : Model τ L Id) (kind : {β : Type} → τ β → K) :
    (M.lift PMF).tagged kind = (M.tagged kind).lift PMF := rfl

/-! ## Realisation: one operation, one circuit

`impl` realises the abstract functionality `Mτ` on the concrete `Mσ` if, for
every request, the concrete run's (response, view) is distributed exactly as
drawing the abstract response and letting a simulator invent the concrete
view *from the abstract record only*: the request's public kind and what
`Mτ` declares.  The simulator never sees the response unless `Mτ` leaks it,
and never the request's payload. -/

/-- `impl` realises `Mτ` on `Mσ` (request kinds `kσ`, `kτ`). -/
def Realizes {σ τ : Sig} {L Kσ Kτ : Type} (kσ : {β : Type} → σ β → Kσ) (kτ : {β : Type} → τ β → Kτ)
    (impl : {β : Type} → τ β → Circ σ β) (Mσ : Model σ L PMF) (Mτ : Model τ L PMF) : Prop :=
  ∃ Sim : Kτ → List L → PMF (List (Kσ × List L)), ∀ {β : Type} (o : τ β),
    dist (Mσ.tagged kσ) (impl o) = do
      let y ← Mτ.program o
      let s ← Sim (kτ o) (Mτ.leak o y)
      pure (y, s)

/-- Statistical version: within `ε` per request. -/
def RealizesStat {σ τ : Sig} {L Kσ Kτ : Type} (kσ : {β : Type} → σ β → Kσ) (kτ : {β : Type} → τ β → Kτ)
    (ε : ENNReal) (impl : {β : Type} → τ β → Circ σ β) (Mσ : Model σ L PMF) (Mτ : Model τ L PMF) : Prop :=
  ∃ Sim : Kτ → List L → PMF (List (Kσ × List L)), ∀ {β : Type} (o : τ β),
    PMF.statDist (dist (Mσ.tagged kσ) (impl o))
      (do let y ← Mτ.program o; let s ← Sim (kτ o) (Mτ.leak o y); pure (y, s)) ≤ ε

/-! ## Statistical distance: the facts used -/

theorem PMF.statDist_self {β : Type} (p : PMF β) : PMF.statDist p p = 0 := by
  simp [PMF.statDist]

theorem PMF.statDist_eq_zero_of_eq {β : Type} {p q : PMF β} (h : p = q) : PMF.statDist p q = 0 := by
  subst h; exact PMF.statDist_self p

/-- Zero distance is equality (both sides are probability distributions). -/
theorem PMF.eq_of_statDist_eq_zero {β : Type} {p q : PMF β} (h : PMF.statDist p q = 0) : p = q := by
  have le : ∀ b, p b ≤ q b := fun b =>
    tsub_eq_zero_iff_le.1 ((ENNReal.tsum_eq_zero.1 h) b)
  ext b
  by_contra hb
  have lt : p b < q b := lt_of_le_of_ne (le b) hb
  have := ENNReal.tsum_lt_tsum (i := b) (by rw [p.tsum_coe]; exact ENNReal.one_ne_top) le lt
  rw [p.tsum_coe, q.tsum_coe] at this
  exact lt_irrefl _ this

/-! ## Example: the Beaver handler realises `Std` on `Pre`

The kind of a request is which feature it belongs to.  The simulator for
`mult` produces the records of the Beaver run: a triple (leaking nothing),
two linear operations, two reveals of a fresh uniform pair, and the free
linear tail.  For the pass-through operations it replays the record. -/

section Beaver
open Examples
variable (F : Type) [Field F] [Fintype F]
local notation "𝕀" => Domain.ideal F

/-- The handler behind `onPre`: Beaver for `mult`, pass-through otherwise. -/
def preHandler : {β : Type} → Std 𝕀 β → Circ (Pre 𝕀) β := fun o => match o with
  | .inl o => Circ.op o
  | .inr (.inl o) => beaver o
  | .inr (.inr o) => Circ.op o

/-- The public kind of a `Std` request: linear, multiplication, reveal. -/
def Std.kind {D : Domain} : {β : Type} → Std D β → Fin 3
  | _, .inl _ => 0 | _, .inr (.inl _) => 1 | _, .inr (.inr _) => 2
/-- The public kind of a `Pre` request: linear, reveal, triple. -/
def Pre.kind {D : Domain} : {β : Type} → Pre D β → Fin 3
  | _, .inl _ => 0 | _, .inr (.inl _) => 1 | _, .inr (.inr _) => 2

/-- The view of a Beaver multiplication: the two opened values are a uniform pair. -/
def beaverView (q : F × F) : List (Fin 3 × List F) :=
  [(2, []), (0, []), (1, [q.1]), (0, []), (1, [q.2]), (0, []), (0, []), (0, []), (0, []), (0, []), (0, [])]

/-- Beaver multiplication, as a distribution over (result, view). -/
theorem dist_beaver (x y : F) :
    dist ((Pre.ideal F).tagged Pre.kind) (beaver (D := 𝕀) (σ := Pre 𝕀) (Mult.mult x y))
      = (PMF.uniformOfFintype (F × F)).bind fun q => pure (x * y, beaverView F q) := by
  have real : dist ((Pre.ideal F).tagged Pre.kind) (beaver (D := 𝕀) (σ := Pre 𝕀) (Mult.mult x y)) =
      (uniform (Fin 2 → F)).bind fun v => pure (x * y, beaverView F (x - v 0, y - v 1)) := by
    simp [dist, beaver, beaverView, Pre.ideal, Pre.kind, Model.tagged, Model.sum, Lin.ideal, Reveal.ideal,
      MulTriple.ideal, Correlation.sample, MulTriple.corr, sub, reveal, smul, add, const, mulTriple,
      Circ.op, Has.inj, run, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.monad_map_eq_map,
      PMF.map_bind, PMF.pure_map, PMF.bind_map, Function.comp_def]
    congr 1
    funext v
    rw [beaver_correct]
  rw [real]
  let e : (Fin 2 → F) ≃ F × F :=
    (piFinTwoEquiv fun _ => F).trans ((Equiv.subLeft x).prodCongr (Equiv.subLeft y))
  rw [← uniform_map_equiv e, PMF.bind_map]
  rfl

/-- **`onPre` realises the arithmetic black box on the preprocessing
functionality.**  The simulator for `mult` draws a fresh uniform pair; the
others replay the abstract record. -/
theorem preHandler_realizes :
    Realizes Pre.kind Std.kind (preHandler F) (Pre.ideal F) ((Std.ideal F).lift PMF) := by
  refine ⟨fun k l =>
    if k = 1 then (PMF.uniformOfFintype (F × F)).map (beaverView F)
    else if k = 0 then pure [(0, l)] else pure [(1, l)], ?_⟩
  intro β o
  dsimp only
  rcases o with o | ⟨x, y⟩ | o
  · cases o <;> simp [preHandler, dist, Circ.op, Pre.ideal, Pre.kind, Model.tagged, Model.sum, Lin.ideal, run,
      Has.inj, Std.kind, Std.ideal]
  · rw [show preHandler F (.inr (.inl (Mult.mult x y))) = beaver (Mult.mult x y) from rfl, dist_beaver]
    simp [Std.kind, Std.ideal, Model.sum, Mult.ideal, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
      PMF.bind_map, Function.comp_def]
  · cases o <;> simp [preHandler, dist, Circ.op, Pre.ideal, Pre.kind, Model.tagged, Model.sum, Reveal.ideal, run,
      Has.inj, Std.kind, Std.ideal]
end Beaver

end Glean
