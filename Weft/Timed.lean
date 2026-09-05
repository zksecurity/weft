import Weft.Model

/-!
# Cost: the timed domain

A functionality is behaviour only.  Cost appears when a hybrid is
*instantiated* in a model that does the behaviour and something more:
here, a model in the scheduling monad `Sched`, where every share carries
the round at which it becomes available and the state carries the clocks
and a communication counter.  An operation's result is available at
`max(operand times, clock) + latency`, so the delay of a program is the
longest path through its dependency hypergraph, computed, not proved;
and each operation adds its communication to the counter.  Delay and
communication are read off one scheduled run (`delayOn`, `commOn`).

Two clocks in the scheduling state cover what the dependency graph cannot
see, because clear values are plain and carry no time: the *reveal clock*
(the latest time a value became clear), which an operation with a clear
argument inherits since clear computation is opaque, and the *control
clock*, raised to the reveal clock by a barrier where a program branches
on a revealed value.  Both over-approximate a dependency edge of weight
zero whose source the interpreter cannot see.

A timed model is a model of an *interface*, chosen by the cost model that
instantiates the hybrid (`Weft.MPC`), never a property of a
functionality.  One generic timed model serves every interface
(`Model.timed`): from an evaluation model and a price per operation it
reads the operand times, the response shape and the interface's
scheduling metadata (`Interface.clearArg`, `Interface.barrier`); a
functionality at a price is then an MPC entry (`Functionality.priced`).
Any other model of the interface may be used instead, a per-input
profile for instance.  The exact instantiation of an abstract operation
under a realisation is to run the implementation (`Realization.timed`,
`Weft.Cost`).
-/
namespace Weft

/-- The price of an operation under a cost model: its latency (rounds)
and its communication. -/
structure Price where
  delay : Nat
  comm : Nat
  deriving DecidableEq, Repr

/-- Scheduling state: the two clocks and the communication so far. -/
structure Clock where
  /-- Control clock: nothing issued after a barrier starts before it. -/
  clock : Nat := 0
  /-- Reveal clock: the latest time at which a value became clear. -/
  revealed : Nat := 0
  /-- Communication counter. -/
  comm : Nat := 0

/-- The scheduling monad: evaluation with a clock.  `StateT`'s `bind` takes
the state pair apart by a pattern, which forces a request's step once and
binds its components; a projection-based bind re-runs the step at every
later use of a response, which is exponential in the number of requests. -/
abbrev Sched : Type → Type := StateT Clock Id

/-- A value together with the round at which it is available. -/
structure Timed (T : Type) where
  val : T
  time : Nat

/-- The timed domain: shares carry a ready time, clear values are plain. -/
abbrev Domain.timed : Domain := ⟨Timed⟩

/-- A share available at round 0. -/
abbrev Timed.now {T : Type} (x : T) : Timed T := ⟨x, 0⟩

namespace Shape

/-- Forget the times of a response. -/
def untime : (s : Shape) → s.interp .timed → s.interp .ideal
  | unit, _ => ()
  | clear _, x => x
  | share _, x => x.val
  | prod a b, p => (a.untime p.1, b.untime p.2)
  | vec _ a, f => fun i => a.untime (f i)
  | list a, xs => xs.map a.untime

/-- Time every share of a response at `t`. -/
def retime (t : Nat) : (s : Shape) → s.interp .ideal → s.interp .timed
  | unit, _ => ()
  | clear _, x => x
  | share _, x => ⟨x, t⟩
  | prod a b, p => (a.retime t p.1, b.retime t p.2)
  | vec _ a, f => fun i => a.retime t (f i)
  | list a, xs => xs.map (a.retime t)

/-- `retime`, in continuation-passing form: the shape is matched once, at
the head, so that the continuation receives a constructor.  This is what
keeps evaluation by `rfl` linear: a share's ready time is then one
projection away, instead of a shape dispatch at every use. -/
def withTimed {β : Type} (t : Nat) : (s : Shape) → s.interp .ideal → (s.interp .timed → β) → β
  | unit, _, k => k ()
  | clear _, x, k => k x
  | share _, x, k => k ⟨x, t⟩
  | prod a b, p, k => k (a.retime t p.1, b.retime t p.2)
  | vec _ a, f, k => k fun i => a.retime t (f i)
  | list a, xs, k => k (xs.map (a.retime t))

end Shape

/-- The ready times of the operands. -/
def Operands.times {Ts : List Type} (a : Operands .timed Ts) : List Nat := a.toList Timed.time
/-- The operands, with their times forgotten. -/
def Operands.untime {Ts : List Type} (a : Operands .timed Ts) : Operands .ideal Ts := a.map Timed.val

/-- Pay for a request.  A free request returns the state object itself
rather than a wrapper around it: the scheduling state is threaded through
every request, and under call-by-name evaluation a wrapper per request is
re-forced from every later reference. -/
def Clock.pay (c : Nat) (s : Clock) : Clock :=
  match c with
  | 0 => s
  | c => { s with comm := s.comm + c }

/-- Advance the clocks after a request: the control clock if the operation
is a barrier, the reveal clock if its response has a clear component.  The
flags are matched at the head, for the reason given at `Clock.pay`. -/
def Clock.after (barrier clear : Bool) (t : Nat) (s : Clock) : Clock :=
  match barrier, clear with
  | false, false => s
  | true, false => { s with clock := max s.clock s.revealed }
  | false, true => { s with revealed := max s.revealed t }
  | true, true => { s with clock := max s.clock s.revealed, revealed := max s.revealed t }

/-- When a request's response is ready, before its latency: the latest of
the operand times and the control clock, and the reveal clock too for an
operation with a clear argument. -/
def Req.base {ι : Interface} (r : Req ι .timed) (s : Clock) : Nat :=
  if ι.clearArg r.op then max (r.args.times.foldr max s.clock) s.revealed else r.args.times.foldr max s.clock

/-- **The generic timed model.**  From an evaluation model and a price per
operation: the response is ready `delay` after the operands and the
control clock (and the reveal clock, for an operation with a clear
argument); a clear response raises the reveal clock; a barrier raises the
control clock; the communication is paid.  Written without `let`: a bound
term is substituted at each use under call-by-name evaluation, and a
response computed twice per request is exponential in the run. -/
def Model.timed {ι : Interface} (E : Model ι .ideal Id) (p : ι.Op → Price) : Model ι .timed Sched where
  step r := fun s =>
    match (E.step ⟨r.op, r.args.untime⟩).run with
    | (y, d) =>
      Shape.withTimed (r.base s + (p r.op).delay) (ι.cod r.op) y fun y' =>
        ((y', d), (Clock.after (ι.barrier r.op) (ι.cod r.op).hasClear (r.base s + (p r.op).delay) s).pay (p r.op).comm)

section Delay
variable {ι : Interface} {α : Type}

/-- A scheduled run: output and final clocks (inputs available at round 0). -/
def Sched.run (M : Model ι .timed Sched) (c : Prog ι .timed α) : α × Clock :=
  let p := Id.run (StateT.run (Weft.run M CostModel.unit c) {})
  (p.1.1, p.2)

/-- The output of a scheduled run. -/
def Sched.output (M : Model ι .timed Sched) (c : Prog ι .timed α) : α := (Sched.run M c).1

/-- The delay of a program with a shared output: when it is available. -/
def delayOn {T : Type} (M : Model ι .timed Sched) (c : Prog ι .timed (Timed T)) : Nat :=
  (Sched.output M c).time

/-- The delay of a program with a clear output: the time of its last reveal. -/
def delayClear (M : Model ι .timed Sched) (c : Prog ι .timed α) : Nat :=
  (Sched.run M c).2.revealed

/-- The communication of a program: what the run paid. -/
def commOn (M : Model ι .timed Sched) (c : Prog ι .timed α) : Nat :=
  (Sched.run M c).2.comm

end Delay
end Weft
