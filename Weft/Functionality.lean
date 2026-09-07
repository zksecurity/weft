import Weft.Model

/-!
# Functionalities and hybrids

A functionality specifies a joint response and disclosure for each request.
Its ideal model is total and may inspect operands.
Programs access the functionality through its interface.

A hybrid is a list of functionalities.
Requests identify a component by position,
and the hybrid model dispatches to that component's model.
`Has F fs` records a position in `fs` and an equality with `F`;
this equality transports the request and response types.
-/
namespace Weft

/-- An interface with a uniquely specified ideal model.

`eval` fixes the random coins for deterministic evaluation.
`IsModel` specifies the probabilistic model as a predicate,
keeping the functionality value computable despite the noncomputable `PMF` model.
This allows computable programs to mention literal hybrids.

For a model `M`, set `IsModel := (· = M)` and use `model_eq` to recover it. -/
structure Functionality where
  ops : Interface
  eval : Model ops .ideal Id
  IsModel : Model ops .ideal PMF → Prop
  isModel_unique : ∃! M, IsModel M

namespace Functionality

/-- The semantics: the unique model the functionality specifies. -/
noncomputable def model (F : Functionality) : Model F.ops .ideal PMF :=
  F.isModel_unique.exists.choose

theorem isModel_model (F : Functionality) : F.IsModel F.model :=
  F.isModel_unique.exists.choose_spec

/-- Identify the selected model using uniqueness. -/
theorem model_eq {F : Functionality} {M : Model F.ops .ideal PMF} (h : F.IsModel M) : F.model = M :=
  F.isModel_unique.unique F.isModel_model h

/-- `(· = M)` is uniquely satisfied. -/
theorem unique_eq {ι : Interface} (M : Model ι .ideal PMF) : ∃! N : Model ι .ideal PMF, N = M :=
  ⟨M, rfl, fun _ h => h⟩

/-- A deterministic functionality: its evaluation model is its semantics. -/
abbrev ofEval (ι : Interface) (E : Model ι .ideal Id) : Functionality :=
  ⟨ι, E, (· = E.lift PMF), unique_eq _⟩

@[simp] theorem ofEval_ops (ι : Interface) (E : Model ι .ideal Id) : (ofEval ι E).ops = ι := rfl
@[simp] theorem ofEval_eval (ι : Interface) (E : Model ι .ideal Id) : (ofEval ι E).eval = E := rfl
@[simp] theorem ofEval_model (ι : Interface) (E : Model ι .ideal Id) : (ofEval ι E).model = E.lift PMF :=
  model_eq rfl

/-- The response marginal of the semantics. -/
noncomputable abbrev program (F : Functionality) (r : Req F.ops .ideal) : PMF (Resp F.ops .ideal r.op) :=
  F.model.program r

end Functionality

/-- Functionalities available to a program. -/
abbrev Hybrid := List Functionality

namespace Hybrid

/-- Select a component by position.
Reducibility lets Lean compute the interface of a literal hybrid during unification. -/
@[reducible] def get : (fs : Hybrid) → Fin fs.length → Functionality
  | F :: _, ⟨0, _⟩ => F
  | _ :: fs, ⟨n + 1, h⟩ => get fs ⟨n, Nat.lt_of_succ_lt_succ h⟩

theorem get_eq (fs : Hybrid) (i : Fin fs.length) : fs.get i = List.get fs i := by
  induction fs with
  | nil => exact i.elim0
  | cons F fs ih => rcases i with ⟨_ | n, h⟩ <;> simp [get, ih]

/-- The interface of a hybrid: an operation of one of its components, by position. -/
@[reducible] def ops (fs : Hybrid) : Interface where
  Op := (i : Fin fs.length) × (fs.get i).ops.Op
  dom o := (fs.get o.1).ops.dom o.2
  cod o := (fs.get o.1).ops.cod o.2
  leak o := (fs.get o.1).ops.leak o.2

/-- The semantics of a hybrid: dispatch to the component's ideal model. -/
noncomputable def model (fs : Hybrid) : Model fs.ops .ideal PMF where
  step r := (fs.get r.op.1).model.step ⟨r.op.2, r.args⟩

/-- The evaluation model of a hybrid. -/
def eval (fs : Hybrid) : Model fs.ops .ideal Id where
  step r := (fs.get r.op.1).eval.step ⟨r.op.2, r.args⟩

theorem model_step (fs : Hybrid) (i : Fin fs.length) (o : (fs.get i).ops.Op)
    (a : Operands .ideal ((fs.get i).ops.dom o)) :
    fs.model.step ⟨⟨i, o⟩, a⟩ = (fs.get i).model.step ⟨o, a⟩ := rfl
theorem eval_step (fs : Hybrid) (i : Fin fs.length) (o : (fs.get i).ops.Op)
    (a : Operands .ideal ((fs.get i).ops.dom o)) :
    fs.eval.step ⟨⟨i, o⟩, a⟩ = (fs.get i).eval.step ⟨o, a⟩ := rfl

/-- A hybrid of lifted evaluation models is itself a lifted evaluation model. -/
theorem model_lift (fs : Hybrid) (h : ∀ i, (fs.get i).model = (fs.get i).eval.lift PMF) :
    fs.model = fs.eval.lift PMF := by
  apply Model.ext
  intro r
  show (fs.get r.op.1).model.step ⟨r.op.2, r.args⟩ = _
  rw [h r.op.1]
  rfl

/-- The first position of a non-empty hybrid. -/
abbrev head (F : Functionality) (fs : Hybrid) : Fin (F :: fs).length := ⟨0, Nat.zero_lt_succ _⟩
/-- The next position. -/
abbrev next (F : Functionality) (fs : Hybrid) (i : Fin fs.length) : Fin (F :: fs).length :=
  ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩

/-! Simplification rules for dispatch on literal hybrids. -/

@[simp] theorem model_cons_zero (F : Functionality) (fs : Hybrid) (o : F.ops.Op)
    (a : Operands .ideal (F.ops.dom o)) :
    (Hybrid.model (F :: fs)).step ⟨⟨head F fs, o⟩, a⟩ = F.model.step ⟨o, a⟩ := rfl
@[simp] theorem model_cons_succ (F : Functionality) (fs : Hybrid) (i : Fin fs.length) (o : (fs.get i).ops.Op)
    (a : Operands .ideal ((fs.get i).ops.dom o)) :
    (Hybrid.model (F :: fs)).step ⟨⟨next F fs i, o⟩, a⟩ = fs.model.step ⟨⟨i, o⟩, a⟩ := rfl
@[simp] theorem eval_cons_zero (F : Functionality) (fs : Hybrid) (o : F.ops.Op)
    (a : Operands .ideal (F.ops.dom o)) :
    (Hybrid.eval (F :: fs)).step ⟨⟨head F fs, o⟩, a⟩ = F.eval.step ⟨o, a⟩ := rfl
@[simp] theorem eval_cons_succ (F : Functionality) (fs : Hybrid) (i : Fin fs.length) (o : (fs.get i).ops.Op)
    (a : Operands .ideal ((fs.get i).ops.dom o)) :
    (Hybrid.eval (F :: fs)).step ⟨⟨next F fs i, o⟩, a⟩ = fs.eval.step ⟨⟨i, o⟩, a⟩ := rfl

end Hybrid

/-- Membership of `F` in `fs`, witnessed by a position and an equality.
Instance search traverses literal lists. -/
class Has (F : Functionality) (fs : Hybrid) where
  i : Fin fs.length
  eq : fs.get i = F

instance Has.here (F : Functionality) (fs : Hybrid) : Has F (F :: fs) := ⟨Hybrid.head F fs, rfl⟩
instance Has.there (F G : Functionality) (fs : Hybrid) [h : Has F fs] : Has F (G :: fs) :=
  ⟨Hybrid.next G fs h.i, h.eq⟩

/-- Shift an event's component index after prepending a functionality. -/
def Event.shift {fs : Hybrid} (G : Functionality) (e : Event fs.ops) : Event (Hybrid.ops (G :: fs)) :=
  ⟨⟨Hybrid.next G fs e.op.1, e.op.2⟩, e.args, e.out, e.leak⟩

namespace Has
variable {F : Functionality} {fs : Hybrid} [h : Has F fs]

/-- An operation of `F`, as an operation of the hybrid. -/
def op (o : F.ops.Op) : fs.ops.Op :=
  h.eq.rec (motive := fun G _ => G.ops.Op → fs.ops.Op) (fun o => ⟨h.i, o⟩) o

/-- Embed an event at `F`'s position in the hybrid.
Used by the inclusion realisation's simulator. -/
def event (e : Event F.ops) : Event fs.ops :=
  h.eq.rec (motive := fun G _ => Event G.ops → Event fs.ops) (fun e => ⟨⟨h.i, e.op⟩, e.args, e.out, e.leak⟩) e

omit h in
@[simp] theorem event_here (e : Event F.ops) :
    event (fs := F :: fs) (h := Has.here F fs) e = ⟨⟨Hybrid.head F fs, e.op⟩, e.args, e.out, e.leak⟩ := rfl

@[simp] theorem event_there (G : Functionality) (e : Event F.ops) :
    event (fs := G :: fs) (h := Has.there F G fs) e = (event (h := h) e).shift G := by
  obtain ⟨i, eq⟩ := h
  subst eq
  rfl

omit h in
@[simp] theorem op_here (o : F.ops.Op) :
    op (fs := F :: fs) (h := Has.here F fs) o = ⟨Hybrid.head F fs, o⟩ := rfl

@[simp] theorem op_there (G : Functionality) (o : F.ops.Op) :
    op (fs := G :: fs) (h := Has.there F G fs) o = ⟨Hybrid.next G fs (op (h := h) o).1, (op (h := h) o).2⟩ := by
  obtain ⟨i, eq⟩ := h
  subst eq
  rfl

end Has

namespace Prog
variable {D : Domain}

/-- Issue a request to component `i` of the hybrid. -/
def opAt (fs : Hybrid) (i : Fin fs.length) (r : Req (fs.get i).ops D) :
    Prog fs.ops D (Resp (fs.get i).ops D r.op) :=
  .call ⟨⟨i, r.op⟩, r.args⟩ .pure

/-- Issue a request using `Has` to transport its types.
For literal hybrids, the membership equality reduces to `rfl`. -/
def op {fs : Hybrid} {F : Functionality} [h : Has F fs] (r : Req F.ops D) :
    Prog fs.ops D (Resp F.ops D r.op) :=
  (h.eq.rec (motive := fun G _ => (r : Req G.ops D) → Prog fs.ops D (Resp G.ops D r.op))
    (opAt fs h.i)) r

/-- Issue a request to the first component.
Keeping its interface explicit lets `simp` match the response type. -/
def opHead (F : Functionality) (fs : Hybrid) (r : Req F.ops D) :
    Prog (Hybrid.ops (F :: fs)) D (Resp F.ops D r.op) :=
  .call ⟨⟨Hybrid.head F fs, r.op⟩, r.args⟩ .pure

/-- Shift a program's requests after prepending a functionality. -/
def lift {fs : Hybrid} (G : Functionality) {α : Type} : Prog fs.ops D α → Prog (Hybrid.ops (G :: fs)) D α :=
  handle fun r => .call ⟨⟨Hybrid.next G fs r.op.1, r.op.2⟩, r.args⟩ .pure

@[simp] theorem op_here {F : Functionality} {fs : Hybrid} (r : Req F.ops D) :
    op (fs := F :: fs) (h := Has.here F fs) r = opHead F fs r := rfl

@[simp] theorem op_there {F G : Functionality} {fs : Hybrid} [h : Has F fs] (r : Req F.ops D) :
    op (fs := G :: fs) (h := Has.there F G fs) r = lift G (op (h := h) r) := by
  obtain ⟨i, e⟩ := h
  subst e
  rfl

end Prog

/-- Every component of `fs` is available in `gs`. -/
class Incl (fs gs : Hybrid) where
  has : (i : Fin fs.length) → Has (fs.get i) gs

instance Incl.refl (fs : Hybrid) : Incl fs fs := ⟨fun i => ⟨i, rfl⟩⟩
instance Incl.nil (gs : Hybrid) : Incl [] gs := ⟨fun i => i.elim0⟩
instance Incl.cons (F : Functionality) (fs gs : Hybrid) [hF : Has F gs] [hs : Incl fs gs] : Incl (F :: fs) gs :=
  ⟨fun i => match i with
    | ⟨0, _⟩ => hF
    | ⟨n + 1, h⟩ => hs.has ⟨n, Nat.lt_of_succ_lt_succ h⟩⟩

namespace Prog
variable {D : Domain} {α : Type}

/-- Embed a program using the supplied component memberships. -/
def weaken {fs gs : Hybrid} [s : Incl fs gs] : Prog fs.ops D α → Prog gs.ops D α :=
  handle fun r => @op D gs (fs.get r.op.1) (s.has r.op.1) ⟨r.op.2, r.args⟩

end Prog

/-! ### Evaluation through `Has` -/

section Generic
variable {fs : Hybrid} {F : Functionality} [h : Has F fs]

/-- A request evaluates to the selected functionality's response. -/
theorem output_op (r : Req F.ops .ideal) :
    output fs.eval (Prog.op r) = (F.eval.step r).run.1 := by
  obtain ⟨i, e⟩ := h
  subst e
  rfl

/-- A request records the selected functionality's event. -/
theorem view_op (r : Req F.ops .ideal) :
    view fs.eval (Prog.op r)
      = [Has.event ⟨r.op, r.args.blank, (F.ops.cod r.op).blank (F.eval.step r).run.1, (F.eval.step r).run.2⟩] := by
  obtain ⟨i, e⟩ := h
  subst e
  rfl

/-- Joint response and event distribution of a request through `Has`. -/
theorem dist_op (r : Req F.ops .ideal) :
    dist fs.model (Prog.op r) = (do
      let (y, d) ← F.model.step r
      pure (y, [Has.event ⟨r.op, r.args.blank, (F.ops.cod r.op).blank y, d⟩])) := by
  obtain ⟨i, e⟩ := h
  subst e
  simp [dist, Prog.op, Prog.opAt, Has.event, run, Trace.seq]
  rfl
end Generic

end Weft
