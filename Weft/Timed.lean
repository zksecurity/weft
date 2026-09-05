import Weft.Model

/-!
# Cost: the timed domain

A functionality is behaviour only.  Cost appears when a hybrid is
*instantiated* in a model that does the behaviour and something more:
here, a model in the scheduling monad `Sched`, where every value, share
or clear, carries the round at which it becomes available, and the state
carries the program's clock and a communication counter.  An operation's
result is available at `max (operand times, now) + latency`, so the delay
of a program is the longest path through its dependency hypergraph,
computed, not proved; and each operation adds its communication to the
counter.  Delay and communication are read off one scheduled run
(`delayOn`, `commOn`).

Clear values are timed too (`Domain.timed.cl := Timed`): an opened value
carries the round at which it was opened, computation on clear values
takes the latest of its inputs, and a scalar computed from an opened
value is an ordinary data edge.  The one piece of state, `now`, is the
round at which the program is issuing requests: it advances only when
the program looks at a clear value (`Prog.look`), since what is issued
after a look cannot be issued before the value is known.  A program that
never looks is a circuit, and `now` stays at 0.

A timed model is a model of an *interface*, chosen by the cost model that
instantiates the hybrid (`Weft.MPC`), never a property of a
functionality.  One generic timed model serves every interface
(`Model.timed`): from an evaluation model and a price per operation it
reads the operand times and the response shape; a functionality at a
price is then an MPC entry (`Functionality.priced`).  Any other model of
the interface may be used instead, a per-input profile for instance.  The
exact instantiation of an abstract operation under a realisation is to
run the implementation (`Realization.timed`, `Weft.Cost`).
-/
namespace Weft

/-- The price of an operation under a cost model: its latency (rounds)
and its communication. -/
structure Price where
  delay : Nat
  comm : Nat
  deriving DecidableEq, Repr

/-- Scheduling state: the program's clock and the communication so far. -/
structure Clock where
  /-- `now`: the round at which the program is issuing requests.  Advanced
  by `Prog.look` only. -/
  clock : Nat := 0
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

namespace Timed
/-- Apply a timed function to a timed argument: ready when both are. -/
def seq {A B : Type} (f : Timed (A → B)) (x : Timed A) : Timed B := ⟨f.val x.val, max f.time x.time⟩
/-- Timed values combine by taking the latest input. -/
abbrev applicative : Applicative Timed where
  map f x := ⟨f x.val, x.time⟩
  pure x := ⟨x, 0⟩
  seq f x := Timed.seq f (x ())
end Timed

/-- The timed domain: shares and clear values carry a ready time. -/
abbrev Domain.timed : Domain := ⟨Timed, Timed, Timed.applicative⟩

/-- A value available at round 0. -/
abbrev Timed.now {T : Type} (x : T) : Timed T := ⟨x, 0⟩
/-- A program-time value is available at round 0 (`Domain.timed.cl T` unfolds
to `Timed T`, which the generic coercion does not match). -/
instance {T : Type} : Coe T (Timed T) := ⟨Timed.now⟩

/-- Looking at a clear value advances the program's clock to its time. -/
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

/-- Time every share of a response at `t`. -/
def retime (t : Nat) : (s : Shape) → s.interp .ideal → s.interp .timed
  | unit, _ => ()
  | clear _, x => ⟨x, t⟩
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
  | clear _, x, k => k ⟨x, t⟩
  | share _, x, k => k ⟨x, t⟩
  | prod a b, p, k => k (a.retime t p.1, b.retime t p.2)
  | vec _ a, f, k => k fun i => a.retime t (f i)
  | list a, xs, k => k (xs.map (a.retime t))

end Shape

/-- When a timed value is ready: the latest of its components. -/
def Shape.ready : (s : Shape) → s.interp .timed → Nat
  | unit, _ => 0
  | clear _, x => x.time
  | share _, x => x.time
  | prod a b, p => max (a.ready p.1) (b.ready p.2)
  | vec _ a, f => (List.finRange _).foldr (fun i m => max (a.ready (f i)) m) 0
  | list a, xs => xs.foldr (fun x m => max (a.ready x) m) 0

/-- When the operands are ready, at the latest. -/
def Operands.ready : {ss : List Shape} → Operands .timed ss → Nat
  | [], _ => 0
  | s :: _, p => max (s.ready p.1) (ready p.2)
/-- The operands, with their times forgotten. -/
def Operands.untime {ss : List Shape} (a : Operands .timed ss) : Operands .ideal ss := a.map Shape.untime

/-- Pay for a request.  A free request returns the state object itself
rather than a wrapper around it: the scheduling state is threaded through
every request, and under call-by-name evaluation a wrapper per request is
re-forced from every later reference. -/
def Clock.pay (c : Nat) (s : Clock) : Clock :=
  match c with
  | 0 => s
  | c => { s with comm := s.comm + c }

/-- When a request can be issued: the latest of its operands and `now`. -/
def Req.base {ι : Interface} (r : Req ι .timed) (s : Clock) : Nat := max r.args.ready s.clock

/-- **The generic timed model.**  From an evaluation model and a price per
operation: the response is ready `delay` after the request can be issued,
and the communication is paid.  Written without `let`: a bound term is
substituted at each use under call-by-name evaluation, and a response
computed twice per request is exponential in the run. -/
def Model.timed {ι : Interface} (E : Model ι .ideal Id) (p : ι.Op → Price) : Model ι .timed Sched where
  step r := fun s =>
    match (E.step ⟨r.op, r.args.untime⟩).run with
    | (y, d) => Shape.withTimed (r.base s + (p r.op).delay) (ι.cod r.op) y fun y' => ((y', d), s.pay (p r.op).comm)

section Delay
variable {ι : Interface} {α : Type}

/-- A scheduled run: output and final clocks (inputs available at round 0). -/
def Sched.run (M : Model ι .timed Sched) (c : Prog ι .timed α) : α × Clock :=
  let p := Id.run (StateT.run (Weft.run M CostModel.unit c) {})
  (p.1.1, p.2)

/-- The output of a scheduled run. -/
def Sched.output (M : Model ι .timed Sched) (c : Prog ι .timed α) : α := (Sched.run M c).1

/-- When a run is done: its output is available and the program has issued
everything (`now`, which a look may have advanced past the output). -/
def Sched.done {T : Type} (p : Timed T × Clock) : Nat := max p.1.time p.2.clock

/-- The delay of a program: when its output, share or clear, is available
and the program is done. -/
def delayOn {T : Type} (M : Model ι .timed Sched) (c : Prog ι .timed (Timed T)) : Nat :=
  Sched.done (Sched.run M c)

/-- `now` at the end of a run: when the program has issued everything.  The
delay of a program whose output is not a timed value (a plain result
assembled from looks). -/
def Sched.now (M : Model ι .timed Sched) (c : Prog ι .timed α) : Nat := (Sched.run M c).2.clock

/-- The communication of a program: what the run paid. -/
def commOn (M : Model ι .timed Sched) (c : Prog ι .timed α) : Nat :=
  (Sched.run M c).2.comm

end Delay
end Weft
