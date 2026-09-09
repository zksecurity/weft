import Weft.Model

/-!
# Timing and communication

Both shared and clear values carry an availability round.
The availability round under `Model.timed` is:
`max (operand times, clock) + latency`.
The operation also adds its communication cost to the counter.

Clear-value arithmetic takes the latest input time.
`Prog.look` advances the clock to the value's availability round,
since subsequent requests may depend on its contents.
Without `look`, independent requests can start in the same round.

An MPC chooses a timed model for each functionality (`Weft.MPC`).
`Model.timed` uses a price per operation;
`Realization.timed` runs the implementation to obtain its cost (`Weft.Cost`).
`delayOn` and `commOn` extract delay and communication from a scheduled run.
-/
namespace Weft

/-- Operation latency in rounds and communication cost. -/
structure Price where
  delay : Nat
  comm : Nat
  deriving DecidableEq, Repr

/-- Scheduling state: the program's clock and the communication so far. -/
structure Clock where
  /-- Earliest round for issuing requests.
  `Prog.look` advances it when control flow depends on a clear value. -/
  clock : Nat := 0
  /-- Communication counter. -/
  comm : Nat := 0

/-- Evaluation with scheduling state.
`StateT.bind` matches the state pair, forcing each step once.
A projection-based bind repeats the step at later uses of its response,
causing exponential reduction time. -/
abbrev Sched : Type → Type := StateT Clock Id

/-- A value together with the round at which it is available. -/
structure Timed (T : Type) where
  val : T
  time : Nat

namespace Timed
/-- Apply the function when both it and its argument are available. -/
def seq {A B : Type} (f : Timed (A → B)) (x : Timed A) : Timed B := ⟨f.val x.val, max f.time x.time⟩
/-- Propagate the latest input time through clear-value computation. -/
abbrev applicative : Applicative Timed where
  map f x := ⟨f x.val, x.time⟩
  pure x := ⟨x, 0⟩
  seq f x := Timed.seq f (x ())
end Timed

/-- The timed domain: shares and clear values carry a ready time. -/
abbrev Domain.timed : Domain := ⟨Timed, Timed, Timed.applicative⟩

/-- A value available at round 0. -/
abbrev Timed.now {T : Type} (x : T) : Timed T := ⟨x, 0⟩
/-- Embed a value at round 0.
The generic coercion does not match the unfolded type `Timed T`. -/
instance {T : Type} : Coe T (Timed T) := ⟨Timed.now⟩

/-- Wait until the clear value is available. -/
instance : Look .timed Sched := ⟨fun c s => (c.val, { s with clock := max s.clock c.time })⟩

namespace Shape

/-- Forget the times of a response. -/
def untime : (s : Shape) → s.interp .timed → s.interp .ideal
  | unit, _ => ()
  | clear _, x => x.val
  | share _, x => x.val
  | prod a b, p => (a.untime p.1, b.untime p.2)
  | vec _ a, f => fun i => a.untime (f i)
  | list a, xs => xs.map a.untime

/-- Set every shared and clear component's availability round to `t`. -/
def retime (t : Nat) : (s : Shape) → s.interp .ideal → s.interp .timed
  | unit, _ => ()
  | clear _, x => ⟨x, t⟩
  | share _, x => ⟨x, t⟩
  | prod a b, p => (a.retime t p.1, b.retime t p.2)
  | vec _ a, f => fun i => a.retime t (f i)
  | list a, xs => xs.map (a.retime t)

/-- Continuation-passing form of `retime`.
Matching the outer shape before calling `k` exposes the response constructor,
so later projections need not repeat that match. -/
def withTimed {β : Type} (t : Nat) : (s : Shape) → s.interp .ideal → (s.interp .timed → β) → β
  | unit, _, k => k ()
  | clear _, x, k => k ⟨x, t⟩
  | share _, x, k => k ⟨x, t⟩
  | prod a b, p, k => k (a.retime t p.1, b.retime t p.2)
  | vec _ a, f, k => k fun i => a.retime t (f i)
  | list a, xs, k => k (xs.map (a.retime t))

/-- `withTimed` agrees with applying the continuation to `retime`. -/
theorem withTimed_eq {β : Type} (t : Nat) (s : Shape) (x : s.interp .ideal) (k : s.interp .timed → β) :
    withTimed t s x k = k (retime t s x) := by
  cases s <;> rfl

end Shape

/-- Latest availability round among the components. -/
def Shape.ready : (s : Shape) → s.interp .timed → Nat
  | unit, _ => 0
  | clear _, x => x.time
  | share _, x => x.time
  | prod a b, p => max (a.ready p.1) (b.ready p.2)
  | vec _ a, f => (List.finRange _).foldr (fun i m => max (a.ready (f i)) m) 0
  | list a, xs => xs.foldr (fun x m => max (a.ready x) m) 0

/-- Latest availability round among the operands. -/
def Operands.ready : {ss : List Shape} → Operands .timed ss → Nat
  | [], _ => 0
  | s :: _, p => max (s.ready p.1) (ready p.2)
/-- The operands, with their times forgotten. -/
def Operands.untime {ss : List Shape} (a : Operands .timed ss) : Operands .ideal ss := a.map Shape.untime

/-- Add communication cost.
Return the state unchanged when the cost is zero;
rebuilding it would add reductions at every later use under call-by-name evaluation. -/
def Clock.pay (c : Nat) (s : Clock) : Clock :=
  match c with
  | 0 => s
  | c => { s with comm := s.comm + c }

@[simp] theorem Clock.pay_clock (c : Nat) (s : Clock) : (s.pay c).clock = s.clock := by
  cases c <;> rfl

theorem Clock.pay_comm (c : Nat) (s : Clock) : (s.pay c).comm = s.comm + c := by
  cases c <;> rfl

/-- Earliest issue round allowed by operand and control dependencies. -/
def Req.base {ι : Interface} (r : Req ι .timed) (s : Clock) : Nat := max r.args.ready s.clock

/-- Evaluate a request and charge its operation's price.
The response becomes available after the operand and control dependencies,
plus the operation's latency.

Match the evaluation result to share it during reduction.
A `let` would substitute the computation at each use,
causing repeated evaluation along the run. -/
def Model.timed {ι : Interface} (E : Model ι .ideal Id) (p : ι.Op → Price) : Model ι .timed Sched where
  step r := fun s =>
    match (E.step ⟨r.op, r.args.untime⟩).run with
    | (y, d) => Shape.withTimed (r.base s + (p r.op).delay) (ι.cod r.op) y fun y' => ((y', d), s.pay (p r.op).comm)

/-- Response, disclosure and state update of a priced step. -/
theorem Model.timed_step {ι : Interface} (E : Model ι .ideal Id) (p : ι.Op → Price) (r : Req ι .timed) (s : Clock) :
    (Model.timed E p).step r s =
      ((Shape.retime (r.base s + (p r.op).delay) (ι.cod r.op) (E.step ⟨r.op, r.args.untime⟩).run.1,
        (E.step ⟨r.op, r.args.untime⟩).run.2), s.pay (p r.op).comm) := by
  simp only [Model.timed, Shape.withTimed_eq]

/-- Issuing a priced request leaves the control clock unchanged. -/
theorem Model.timed_clock {ι : Interface} (E : Model ι .ideal Id) (p : ι.Op → Price) (r : Req ι .timed) (s : Clock) :
    ((Model.timed E p).step r s).2.clock = s.clock := by
  rw [Model.timed_step, Clock.pay_clock]

section Delay
variable {ι : Interface} {α : Type}

/-- Run from a zero clock and communication counter.
Input availability times are supplied by the program. -/
def Sched.run (M : Model ι .timed Sched) (c : Prog ι .timed α) : α × Clock :=
  let p := Id.run (StateT.run (Weft.run M CostModel.unit c) {})
  (p.1.1, p.2)

/-- The output of a scheduled run. -/
def Sched.output (M : Model ι .timed Sched) (c : Prog ι .timed α) : α := (Sched.run M c).1

/-- Latest of the output's availability round and the final control clock. -/
def Sched.done {T : Type} (p : Timed T × Clock) : Nat := max p.1.time p.2.clock

/-- Completion round for a program returning a timed value. -/
def delayOn {T : Type} (M : Model ι .timed Sched) (c : Prog ι .timed (Timed T)) : Nat :=
  Sched.done (Sched.run M c)

/-- Completion round for a program returning a structured value. -/
def readyOn (M : Model ι .timed Sched) (s : Shape) (c : Prog ι .timed (s.interp .timed)) : Nat :=
  max (s.ready (Sched.run M c).1) (Sched.run M c).2.clock

theorem readyOn_share {T : Type} (M : Model ι .timed Sched) (c : Prog ι .timed (Timed T)) :
    readyOn M (.share T) c = delayOn M c := rfl

/-- Final control clock.
Use for plain results computed through `look`,
whose dependencies are already accounted for by the clock. -/
def Sched.now (M : Model ι .timed Sched) (c : Prog ι .timed α) : Nat := (Sched.run M c).2.clock

/-- Total communication charged during the run. -/
def commOn (M : Model ι .timed Sched) (c : Prog ι .timed α) : Nat :=
  (Sched.run M c).2.comm

end Delay
end Weft
