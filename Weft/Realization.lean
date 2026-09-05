import Weft.Std.Hybrids

/-!
# Realisations: one certificate, and how it composes

A *realisation* of a functionality `F` over a hybrid `fs` is a program
for every operation of `F` and every domain, a simulator, and the
equation: the program's (response, view) at the ideal domain equals `F`'s
response paired with the simulator's output on `F`'s event.  The
simulator receives the event and nothing else: never a hidden component
of the response, never an operand.  The full response stays in the joint,
because a hidden component may be opened later and the trace must be
consistent with that opening.

This is the only privacy notion.  "This program is private with declared
disclosure `d`" is a realisation of a one-operation functionality whose
model says so.  A gadget is that, at most a word.

A realisation may come with a precondition on requests; the guarantee
holds for valid requests only.  A caller discharges it by `Valid`: every
request it issues, on the support of its ideal run, satisfies the
precondition.  Composition is `Realization.comp`, once: inlining composes
programs, `simList` composes simulators, and the precondition of the
composite is the caller's together with validity of its program for the
callees.
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

/-- `Valid M P c`: every request `c` issues, on the support of its run under
`M`, satisfies `P`.  Inductive on the program, restricted to supported
responses. -/
inductive Valid {ι : Interface} (M : Model ι .ideal PMF) (P : Req ι .ideal → Prop) :
    {α : Type} → Prog ι .ideal α → Prop
  | pure {α : Type} (a : α) : Valid M P (.pure a)
  | call {α : Type} (r : Req ι .ideal) (k : Resp ι .ideal r.op → Prog ι .ideal α)
      (hr : P r) (hk : ∀ z ∈ (M.step r).support, Valid M P (k z.1)) : Valid M P (.call r k)

attribute [simp] Valid.pure

/-- A precondition that always holds is always valid. -/
theorem Valid.of_forall {ι : Interface} (M : Model ι .ideal PMF) {P : Req ι .ideal → Prop} (hP : ∀ r, P r)
    {α : Type} (c : Prog ι .ideal α) : Valid M P c := by
  induction c with
  | pure a => exact .pure a
  | call r k ih => exact .call r k (hP r) fun z _ => ih z.1

/-- Validity for the trivial precondition. -/
theorem Valid.true {ι : Interface} (M : Model ι .ideal PMF) {α : Type} (c : Prog ι .ideal α) :
    Valid M (fun _ => True) c := Valid.of_forall M (fun _ => trivial) c

/-- What a run can produce. -/
theorem mem_support_dist_call {ι : Interface} (M : Model ι .ideal PMF) {α : Type} (r : Req ι .ideal)
    (k : Resp ι .ideal r.op → Prog ι .ideal α) (p : α × List (Event ι)) :
    p ∈ (dist M (.call r k)).support ↔
      ∃ z ∈ (M.step r).support, ∃ q ∈ (dist M (k z.1)).support,
        p = (q.1, ⟨r.op, r.args.blank, (ι.cod r.op).blank z.1, z.2⟩ :: q.2) := by
  rw [dist_call]
  simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.support_bind, PMF.support_pure,
    Set.mem_iUnion, Set.mem_singleton_iff, exists_prop]

/-- Validity of a sequential composition: the first part is valid and,
on every run it can produce, so is the continuation. -/
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

/-- **A realisation.**  `impl` is a program for every domain (it cannot
look inside a share); `Sim` sees only the event; `real` is the equation,
under `Pre`. -/
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

/-- The handler: each request of the hybrid, implemented by its component's realisation. -/
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

/-- **Composition.**  Inlining realisations of every component into a
caller: the concrete run of the inlined program is the abstract run of
the caller with each event replaced by its simulation, for every caller
valid for the realisations' preconditions.  Induction on the caller's
free-monad trace; at each request the realisation equation, and one
commutation of independent draws: the simulator's coins for this request
do not interact with the rest of the run. -/
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

/-- Correctness transports: the output distribution of the inlined program
is the caller's on the abstract hybrid. -/
theorem output_transport {fs gs : Hybrid} (g : Realizations fs gs) {α : Type} (c : Prog fs.ops .ideal α)
    (hc : Valid fs.model g.Pre c) :
    Prod.fst <$> dist gs.model (Prog.handle (g.impl .ideal) c) = Prod.fst <$> dist fs.model c := by
  rw [handle_realizes g c hc]
  simp [PMF.monad_bind_eq_bind, PMF.monad_map_eq_map, PMF.monad_pure_eq_pure, PMF.map_bind, PMF.pure_map,
    PMF.bind_const]
  rfl

namespace Realization

/-- The trusted realisation: calling `F` realises `F` over any hybrid that
contains it.  The simulator replays the event at `F`'s position. -/
noncomputable def incl (F : Functionality) (gs : Hybrid) [h : Has F gs] : Realization F gs where
  impl _ r := Prog.op r
  Sim e := pure [Has.event e]
  real r _ := by rw [dist_op]; simp

/-- **Composition, once.**  Inlining realisations of the components of `fs`
into a realisation over `fs`.  The precondition of the composite is the
outer one together with validity of the outer program for the inner
preconditions. -/
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

/-- Every component available in the target: the trivial realisations. -/
noncomputable def incl : (fs : Hybrid) → (gs : Hybrid) → [Incl fs gs] → Realizations fs gs
  | [], _, _ => .nil
  | F :: fs, gs, s => .cons (Realization.incl F gs (h := s.has ⟨0, Nat.zero_lt_succ _⟩))
      (@incl fs gs ⟨fun i => s.has ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩⟩)

/-- The identity: every component of `fs` realised by itself. -/
noncomputable abbrev id (fs : Hybrid) : Realizations fs fs := incl fs fs

end Realizations

end Weft
