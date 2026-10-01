import Weft.Model

/-!
# Functionalities and hybrids

A functionality specifies one function's joint response and disclosure.
Its signature has fixed operand, response and leakage types.
The ideal model is total and may inspect operands.
Programs select a functionality through membership in a hybrid.

A hybrid is a list of functionalities.
Requests identify a component by position; there is no operation selector within it.
`Has F fs` records a position and an equality with `F`,
which transports operand and response types.
-/
namespace Weft

/-- A single function with a uniquely specified ideal model.

`eval` fixes random coins for deterministic evaluation.
`IsModel` specifies the probabilistic model as a predicate,
keeping the functionality value computable despite its noncomputable semantics.
For a model `M`, set `IsModel := (· = M)` and use `model_eq` to recover it. -/
structure Functionality where
  sig : Signature
  eval : FunctionModel sig .ideal Id
  IsModel : FunctionModel sig .ideal PMF → Prop
  isModel_unique : ∃! M, IsModel M

namespace Functionality

/-- The unique probabilistic function specified by the functionality. -/
noncomputable def model (F : Functionality) : FunctionModel F.sig .ideal PMF :=
  F.isModel_unique.exists.choose

theorem isModel_model (F : Functionality) : F.IsModel F.model :=
  F.isModel_unique.exists.choose_spec

/-- Identify the selected model using uniqueness. -/
theorem model_eq {F : Functionality} {M : FunctionModel F.sig .ideal PMF} (h : F.IsModel M) : F.model = M :=
  F.isModel_unique.unique F.isModel_model h

/-- Equality to a given model is uniquely satisfied. -/
theorem unique_eq {σ : Signature} (M : FunctionModel σ .ideal PMF) : ∃! N : FunctionModel σ .ideal PMF, N = M :=
  ⟨M, rfl, fun _ h => h⟩

/-- A deterministic functionality, with point-mass probabilistic semantics. -/
abbrev ofEval (σ : Signature) (E : FunctionModel σ .ideal Id) : Functionality :=
  ⟨σ, E, (· = E.lift PMF), unique_eq _⟩

@[simp] theorem ofEval_sig (σ : Signature) (E : FunctionModel σ .ideal Id) : (ofEval σ E).sig = σ := rfl
@[simp] theorem ofEval_eval (σ : Signature) (E : FunctionModel σ .ideal Id) : (ofEval σ E).eval = E := rfl
@[simp] theorem ofEval_model (σ : Signature) (E : FunctionModel σ .ideal Id) : (ofEval σ E).model = E.lift PMF :=
  model_eq rfl

/-- The response marginal. Use `model.step` for the joint law. -/
noncomputable abbrev response (F : Functionality) (a : F.sig.Args .ideal) : PMF (F.sig.Resp .ideal) :=
  F.model.response a

/-- The explicitly declared disclosure marginal. -/
noncomputable abbrev leakage (F : Functionality) (a : F.sig.Args .ideal) : PMF F.sig.leak :=
  F.model.leakage a

end Functionality

/-- Functionalities available to a program. -/
abbrev Hybrid := List Functionality

namespace Hybrid

/-- Select a component by position.
Reducibility lets Lean compute the signature of a literal hybrid during unification. -/
@[reducible] def get : (fs : Hybrid) → Fin fs.length → Functionality
  | F :: _, ⟨0, _⟩ => F
  | _ :: fs, ⟨n + 1, h⟩ => get fs ⟨n, Nat.lt_of_succ_lt_succ h⟩

theorem get_eq (fs : Hybrid) (i : Fin fs.length) : fs.get i = List.get fs i := by
  induction fs with
  | nil => exact i.elim0
  | cons F fs ih => rcases i with ⟨_ | n, h⟩ <;> simp [get, ih]

/-- A hybrid's operation selector is just a functionality's position. -/
@[reducible] def ops (fs : Hybrid) : Interface where
  Op := Fin fs.length
  dom i := (fs.get i).sig.dom
  cod i := (fs.get i).sig.cod
  leak i := (fs.get i).sig.leak

/-- Dispatch a request to the selected functionality's ideal model. -/
noncomputable def model (fs : Hybrid) : Model fs.ops .ideal PMF where
  step r := (fs.get r.op).model.step r.args

/-- Dispatch a request to the selected functionality's evaluation model. -/
def eval (fs : Hybrid) : Model fs.ops .ideal Id where
  step r := (fs.get r.op).eval.step r.args

theorem model_step (fs : Hybrid) (i : Fin fs.length) (a : (fs.get i).sig.Args .ideal) :
    fs.model.step ⟨i, a⟩ = (fs.get i).model.step a := rfl

theorem eval_step (fs : Hybrid) (i : Fin fs.length) (a : (fs.get i).sig.Args .ideal) :
    fs.eval.step ⟨i, a⟩ = (fs.get i).eval.step a := rfl

/-- A hybrid of deterministic functionalities has deterministic semantics. -/
theorem model_lift (fs : Hybrid) (h : ∀ i, (fs.get i).model = (fs.get i).eval.lift PMF) :
    fs.model = fs.eval.lift PMF := by
  apply Model.ext
  intro r
  show (fs.get r.op).model.step r.args = _
  rw [h r.op]
  rfl

/-- The first position of a non-empty hybrid. -/
abbrev head (F : Functionality) (fs : Hybrid) : Fin (F :: fs).length := ⟨0, Nat.zero_lt_succ _⟩
/-- Shift a position after prepending a functionality. -/
abbrev next (F : Functionality) (fs : Hybrid) (i : Fin fs.length) : Fin (F :: fs).length :=
  ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩

@[simp] theorem model_cons_zero (F : Functionality) (fs : Hybrid) (a : F.sig.Args .ideal) :
    (Hybrid.model (F :: fs)).step ⟨head F fs, a⟩ = F.model.step a := rfl
@[simp] theorem model_cons_succ (F : Functionality) (fs : Hybrid) (i : Fin fs.length) (a : (fs.get i).sig.Args .ideal) :
    (Hybrid.model (F :: fs)).step ⟨next F fs i, a⟩ = fs.model.step ⟨i, a⟩ := rfl
@[simp] theorem eval_cons_zero (F : Functionality) (fs : Hybrid) (a : F.sig.Args .ideal) :
    (Hybrid.eval (F :: fs)).step ⟨head F fs, a⟩ = F.eval.step a := rfl
@[simp] theorem eval_cons_succ (F : Functionality) (fs : Hybrid) (i : Fin fs.length) (a : (fs.get i).sig.Args .ideal) :
    (Hybrid.eval (F :: fs)).step ⟨next F fs i, a⟩ = fs.eval.step ⟨i, a⟩ := rfl

end Hybrid

/-- Membership of `F` in `fs`, witnessed by a position and an equality. -/
class Has (F : Functionality) (fs : Hybrid) where
  i : Fin fs.length
  eq : fs.get i = F

instance Has.here (F : Functionality) (fs : Hybrid) : Has F (F :: fs) := ⟨Hybrid.head F fs, rfl⟩
instance Has.there (F G : Functionality) (fs : Hybrid) [h : Has F fs] : Has F (G :: fs) :=
  ⟨Hybrid.next G fs h.i, h.eq⟩

/-- Shift an event's functionality index after prepending a component. -/
def Event.shift {fs : Hybrid} (G : Functionality) (e : Event fs.ops) : Event (Hybrid.ops (G :: fs)) :=
  ⟨Hybrid.next G fs e.op, e.leak⟩

namespace Has
variable {F : Functionality} {fs : Hybrid} [h : Has F fs]

/-- The selected functionality's position in the hybrid. -/
def op : fs.ops.Op := h.i

/-- Embed a functionality's declared leakage as an event at its position. -/
def event (d : F.sig.leak) : Event fs.ops :=
  h.eq.rec (motive := fun G _ => G.sig.leak → Event fs.ops) (fun d => ⟨h.i, d⟩) d

omit h in
@[simp] theorem event_here (d : F.sig.leak) :
    event (fs := F :: fs) (h := Has.here F fs) d = ⟨Hybrid.head F fs, d⟩ := rfl

@[simp] theorem event_there (G : Functionality) (d : F.sig.leak) :
    event (fs := G :: fs) (h := Has.there F G fs) d = (event (h := h) d).shift G := by
  obtain ⟨i, eq⟩ := h
  subst eq
  rfl

omit h in
@[simp] theorem op_here : op (fs := F :: fs) (h := Has.here F fs) = Hybrid.head F fs := rfl

@[simp] theorem op_there (G : Functionality) :
    op (fs := G :: fs) (h := Has.there F G fs) = Hybrid.next G fs (op (h := h)) := rfl

end Has

namespace Prog
variable {D : Domain}

/-- Call the functionality at position `i` with its operands. -/
def opAt (fs : Hybrid) (i : Fin fs.length) (a : (fs.get i).sig.Args D) :
    Prog fs.ops D ((fs.get i).sig.Resp D) := .call ⟨i, a⟩ .pure

/-- Call a functionality using membership to transport its operand and response types. -/
def op {fs : Hybrid} {F : Functionality} [h : Has F fs] (a : F.sig.Args D) : Prog fs.ops D (F.sig.Resp D) :=
  (h.eq.rec (motive := fun G _ => G.sig.Args D → Prog fs.ops D (G.sig.Resp D)) (opAt fs h.i)) a

/-- Call the first functionality. -/
def opHead (F : Functionality) (fs : Hybrid) (a : F.sig.Args D) :
    Prog (Hybrid.ops (F :: fs)) D (F.sig.Resp D) := .call ⟨Hybrid.head F fs, a⟩ .pure

/-- Shift a program's requests after prepending a functionality. -/
def lift {fs : Hybrid} (G : Functionality) {α : Type} : Prog fs.ops D α → Prog (Hybrid.ops (G :: fs)) D α :=
  handle fun r => .call ⟨Hybrid.next G fs r.op, r.args⟩ .pure

@[simp] theorem op_here {F : Functionality} {fs : Hybrid} (a : F.sig.Args D) :
    op (fs := F :: fs) (h := Has.here F fs) a = opHead F fs a := rfl

@[simp] theorem op_there {F G : Functionality} {fs : Hybrid} [h : Has F fs] (a : F.sig.Args D) :
    op (fs := G :: fs) (h := Has.there F G fs) a = lift G (op (h := h) a) := by
  obtain ⟨i, e⟩ := h
  subst e
  rfl

end Prog

/-- Every functionality in `fs` is available in `gs`. -/
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

/-- Embed a program using the supplied functionality memberships. -/
def weaken {fs gs : Hybrid} [s : Incl fs gs] : Prog fs.ops D α → Prog gs.ops D α :=
  handle fun r => @op D gs (fs.get r.op) (s.has r.op) r.args

end Prog

section Generic
variable {fs : Hybrid} {F : Functionality} [h : Has F fs]

/-- A call evaluates to the selected functionality's response. -/
theorem output_op (a : F.sig.Args .ideal) : output fs.eval (Prog.op a) = (F.eval.step a).run.1 := by
  obtain ⟨i, e⟩ := h
  subst e
  rfl

/-- A call records exactly the selected functionality's declared disclosure. -/
theorem view_op (a : F.sig.Args .ideal) :
    view fs.eval (Prog.op a) = [Has.event (F.eval.step a).run.2] := by
  obtain ⟨i, e⟩ := h
  subst e
  rfl

/-- Joint response and event distribution of a functionality call. -/
theorem dist_op (a : F.sig.Args .ideal) :
    dist fs.model (Prog.op a) = (do
      let (y, d) ← F.model.step a
      pure (y, [Has.event d])) := by
  obtain ⟨i, e⟩ := h
  subst e
  simp [dist, Prog.op, Prog.opAt, Has.event, run, Trace.seq]
  rfl

end Generic
end Weft
