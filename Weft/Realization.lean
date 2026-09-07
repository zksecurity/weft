import Weft.Std.Hybrids

/-!
# Realisations and composition

A realisation implements each operation of `F` over a hybrid `fs`.
For requests satisfying `Pre`, the real and simulated joint distributions agree.
The simulated distribution pairs the ideal response with the simulator's view.
The simulator receives `F`'s event:
the operation, clear operands and response components, and declared disclosure.

We retain the full response in the joint distribution.
A shared response may be opened later,
and the simulated view must remain consistent with that opening.

`Valid` requires every request in the support of a caller's ideal run to satisfy `Pre`.
`Realization.comp` inlines implementations and composes their simulators with `simList`.
Its precondition combines the outer precondition with validity for the inner calls.
-/
namespace Weft

/-- Run the per-event simulators along an abstract view. -/
noncomputable def simList {ι κ : Interface} (Sim : Event ι → PMF (List (Event κ))) :
    List (Event ι) → PMF (List (Event κ))
  | [] => pure []
  | e :: es => do
    let s ← Sim e
    let t ← simList Sim es
    pure (s ++ t)

@[simp] theorem simList_nil {ι κ : Interface} (Sim : Event ι → PMF (List (Event κ))) : simList Sim [] = pure [] := rfl
@[simp] theorem simList_cons {ι κ : Interface} (Sim : Event ι → PMF (List (Event κ))) (e : Event ι) (es : List (Event ι)) :
    simList Sim (e :: es) = (do let s ← Sim e; let t ← simList Sim es; pure (s ++ t)) := rfl

/-- Every request reachable under `M` satisfies `P`.
Only responses in the support of the model are considered. -/
inductive Valid {ι : Interface} (M : Model ι .ideal PMF) (P : Req ι .ideal → Prop) :
    {α : Type} → Prog ι .ideal α → Prop
  | pure {α : Type} (a : α) : Valid M P (.pure a)
  | call {α : Type} (r : Req ι .ideal) (k : Resp ι .ideal r.op → Prog ι .ideal α)
      (hr : P r) (hk : ∀ z ∈ (M.step r).support, Valid M P (k z.1)) : Valid M P (.call r k)
  | look {α T : Type} (c : Domain.ideal.clear T) (k : T → Prog ι .ideal α) (hk : Valid M P (k c)) :
      Valid M P (.look c k)

attribute [simp] Valid.pure

/-- A universally satisfied precondition is valid for every program. -/
theorem Valid.of_forall {ι : Interface} (M : Model ι .ideal PMF) {P : Req ι .ideal → Prop} (hP : ∀ r, P r)
    {α : Type} (c : Prog ι .ideal α) : Valid M P c := by
  induction c with
  | pure a => exact .pure a
  | call r k ih => exact .call r k (hP r) fun z _ => ih z.1
  | look c k ih => exact .look c k (ih c)

/-- Validity for the trivial precondition. -/
theorem Valid.true {ι : Interface} (M : Model ι .ideal PMF) {α : Type} (c : Prog ι .ideal α) :
    Valid M (fun _ => True) c := Valid.of_forall M (fun _ => trivial) c

/-- Support of a request followed by a continuation. -/
theorem mem_support_dist_call {ι : Interface} (M : Model ι .ideal PMF) {α : Type} (r : Req ι .ideal)
    (k : Resp ι .ideal r.op → Prog ι .ideal α) (p : α × List (Event ι)) :
    p ∈ (dist M (.call r k)).support ↔
      ∃ z ∈ (M.step r).support, ∃ q ∈ (dist M (k z.1)).support,
        p = (q.1, ⟨r.op, r.args.blank, (ι.cod r.op).blank z.1, z.2⟩ :: q.2) := by
  rw [dist_call]
  simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.support_bind, PMF.support_pure,
    Set.mem_iUnion, Set.mem_singleton_iff, exists_prop]

/-- Sequential composition preserves validity when every reachable continuation is valid. -/
theorem Valid.bind {ι : Interface} {M : Model ι .ideal PMF} {P : Req ι .ideal → Prop} {α β : Type}
    {c : Prog ι .ideal α} {k : α → Prog ι .ideal β} (hc : Valid M P c)
    (hk : ∀ p ∈ (dist M c).support, Valid M P (k p.1)) : Valid M P (Prog.bind c k) := by
  induction c with
  | pure a =>
    exact hk (a, []) (by simp [dist, run, PMF.monad_map_eq_map, PMF.monad_pure_eq_pure])
  | call r k' ih =>
    cases hc with
    | call _ _ hr hk' =>
      exact .call r _ hr fun z hz => ih z.1 (hk' z hz) fun q hq =>
        hk (q.1, ⟨r.op, r.args.blank, (ι.cod r.op).blank z.1, z.2⟩ :: q.2) ((mem_support_dist_call M r k' _).2 ⟨z, hz, q, hq, rfl⟩)
  | look c k' ih =>
    cases hc with
    | look _ _ hk' => exact .look c _ (ih c hk' fun q hq => hk q (by rw [dist_look]; exact hq))

/-- An implementation and simulator with equal joint distributions under `Pre`.
`impl` is polymorphic in the domain;
`Weft.Program` provides the implementation check. -/
structure Realization (F : Functionality) (fs : Hybrid) where
  impl : (D : Domain) → (r : Req F.ops D) → Prog fs.ops D (Resp F.ops D r.op)
  Pre : Req F.ops .ideal → Prop := fun _ => True
  Sim : Event F.ops → PMF (List (Event fs.ops))
  real : ∀ r, Pre r → dist fs.model (impl .ideal r) = (do
    let (y, d) ← F.model.step r
    let s ← Sim ⟨r.op, r.args.blank, (F.ops.cod r.op).blank y, d⟩
    pure (y, s))

/-- Realisations of every component of a hybrid over another. -/
inductive Realizations : Hybrid → Hybrid → Type 1 where
  | nil {gs : Hybrid} : Realizations [] gs
  | cons {F : Functionality} {fs gs : Hybrid} : Realization F gs → Realizations fs gs → Realizations (F :: fs) gs

namespace Realizations
variable {fs gs : Hybrid}

/-- The realisation of the component at a position. -/
def get : {fs : Hybrid} → Realizations fs gs → (i : Fin fs.length) → Realization (fs.get i) gs
  | _, .cons r _, ⟨0, _⟩ => r
  | _, .cons _ rs, ⟨n + 1, h⟩ => rs.get ⟨n, Nat.lt_of_succ_lt_succ h⟩

/-- Dispatch each request to its component's implementation. -/
def impl (g : Realizations fs gs) (D : Domain) (r : Req fs.ops D) : Prog gs.ops D (Resp fs.ops D r.op) :=
  (g.get r.op.1).impl D ⟨r.op.2, r.args⟩

/-- The precondition, per request of the hybrid. -/
def Pre (g : Realizations fs gs) (r : Req fs.ops .ideal) : Prop :=
  (g.get r.op.1).Pre ⟨r.op.2, r.args⟩

/-- The simulator, per event of the hybrid. -/
noncomputable def Sim (g : Realizations fs gs) (e : Event fs.ops) : PMF (List (Event gs.ops)) :=
  (g.get e.op.1).Sim ⟨e.op.2, e.args, e.out, e.leak⟩

theorem real (g : Realizations fs gs) (r : Req fs.ops .ideal) (h : g.Pre r) :
    dist gs.model (g.impl .ideal r) = (do
      let (y, d) ← fs.model.step r
      let s ← g.Sim ⟨r.op, r.args.blank, (fs.ops.cod r.op).blank y, d⟩
      pure (y, s)) := by
  obtain ⟨⟨i, o⟩, a⟩ := r
  exact (g.get i).real ⟨o, a⟩ h

end Realizations

/-- Inlining preserves the caller's joint distribution up to per-event simulation.
The caller must satisfy the realisations' preconditions.

Induct on the caller and apply the realisation equation at each request.
The simulator's fresh coins commute with the continuation's draws. -/
theorem handle_realizes {fs gs : Hybrid} (g : Realizations fs gs) {α : Type} (c : Prog fs.ops .ideal α)
    (hc : Valid fs.model g.Pre c) :
    dist gs.model (Prog.handle (g.impl .ideal) c) = (do
      let r ← dist fs.model c
      let s ← simList g.Sim r.2
      pure (r.1, s)) := by
  induction c with
  | pure a => simp [dist, simList]
  | call r k ih =>
    cases hc with
    | call _ _ hr hk =>
    rw [Prog.handle_call, dist_bind, g.real r hr]
    simp only [dist_call, simList_cons, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
      PMF.bind_bind, PMF.pure_bind]
    refine PMF.bind_congr_support fun z hz => ?_
    rw [ih z.1 (hk z hz)]
    simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind]
    rw [PMF.bind_comm]
  | look c k ih =>
    cases hc with
    | look _ _ hk => rw [Prog.handle_look, dist_look, dist_look]; exact ih c hk

/-- Inlining valid realisations preserves the output distribution. -/
theorem output_transport {fs gs : Hybrid} (g : Realizations fs gs) {α : Type} (c : Prog fs.ops .ideal α)
    (hc : Valid fs.model g.Pre c) :
    Prod.fst <$> dist gs.model (Prog.handle (g.impl .ideal) c) = Prod.fst <$> dist fs.model c := by
  rw [handle_realizes g c hc]
  simp [PMF.monad_bind_eq_bind, PMF.monad_map_eq_map, PMF.monad_pure_eq_pure, PMF.map_bind, PMF.pure_map,
    PMF.bind_const]
  rfl

namespace Realization

/-- Realise `F` by calling it in a hybrid containing it.
The simulator embeds the event at `F`'s position. -/
noncomputable def incl (F : Functionality) (gs : Hybrid) [h : Has F gs] : Realization F gs where
  impl _ r := Prog.op r
  Sim e := pure [Has.event e]
  real r _ := by rw [dist_op]; simp

/-- Inline the realisations of `fs` into `f`.
Require `f.Pre` and validity of `f.impl` for the inner preconditions. -/
noncomputable def comp {F : Functionality} {fs gs : Hybrid} (f : Realization F fs) (g : Realizations fs gs) :
    Realization F gs where
  impl D r := Prog.handle (g.impl D) (f.impl D r)
  Pre r := f.Pre r ∧ Valid fs.model g.Pre (f.impl .ideal r)
  Sim e := do
    let s ← f.Sim e
    simList g.Sim s
  real r hr := by
    rw [handle_realizes g _ hr.2, f.real r hr.1]
    simp [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind]

end Realization

namespace Realizations

/-- Realise each component by its occurrence in the target hybrid. -/
noncomputable def incl : (fs : Hybrid) → (gs : Hybrid) → [Incl fs gs] → Realizations fs gs
  | [], _, _ => .nil
  | F :: fs, gs, s => .cons (Realization.incl F gs (h := s.has ⟨0, Nat.zero_lt_succ _⟩))
      (@incl fs gs ⟨fun i => s.has ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩⟩)

/-- Realise each component by itself. -/
noncomputable abbrev id (fs : Hybrid) : Realizations fs fs := incl fs fs

end Realizations

end Weft
