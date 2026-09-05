import Weft.Functionality

/-!
# Delay: the timed domain

Delay is not accumulated by the interpreter; it is *computed from data
dependencies*.  The same program is run in the **timed domain**, where
every share carries the round at which it becomes available (clear
values stay plain, so programs branch on them as usual).  An operation's
result is available at `max(operand times, clock) + latency`.

Two clocks in the scheduling state cover what the dependency graph cannot
see: the *reveal clock* (the latest time a value became clear), which an
operation with a clear argument inherits since clear computation is
opaque, and the *control clock*, raised to the reveal clock by a barrier
where a program branches on a revealed value.

One generic timed model serves every interface: it takes the
functionality's evaluation model (so reactive programs take the branch the
values dictate) and a latency per operation, and reads the operand times
and the response shape structurally.  Which operations carry a clear
argument, and which are barriers, is the interface's scheduling metadata
(`Interface.pubArg`, `Interface.ctrl`), trusted like the rest of it.

What this gives is the delay of the program as written, under eager
scheduling.  Modelling an abstract operation by a single latency, or by a
per-input profile, is a conservative bound for a reactive callee, not an
exact count: the reveal and control clocks are global state, so an inlined
callee that reveals, computes in the clear and inserts back waits on every
earlier reveal of the caller.  A clock-aware composition statement for
delay is future work (report, Issue 10).
-/
namespace Weft

/-- Scheduling state. -/
structure Clock where
  /-- Control clock: nothing issued after a barrier starts before it. -/
  clock : Nat := 0
  /-- Reveal clock: the latest time at which a value became clear. -/
  revealed : Nat := 0

/-- The scheduling monad: evaluation with a clock. -/
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
  | prod a b, (x, y) => (a.untime x, b.untime y)
  | vec _ a, f => fun i => a.untime (f i)
  | list a, xs => xs.map a.untime

/-- Time every share of a response at `t`. -/
def retime (t : Nat) : (s : Shape) → s.interp .ideal → s.interp .timed
  | unit, _ => ()
  | clear _, x => x
  | share _, x => ⟨x, t⟩
  | prod a b, (x, y) => (a.retime t x, b.retime t y)
  | vec _ a, f => fun i => a.retime t (f i)
  | list a, xs => xs.map (a.retime t)

end Shape

/-- The ready times of the operands. -/
def Operands.times {Ts : List Type} (a : Operands .timed Ts) : List Nat := a.toList Timed.time
/-- The operands, with their times forgotten. -/
def Operands.untime {Ts : List Type} (a : Operands .timed Ts) : Operands .ideal Ts := a.map Timed.val

/-- **The generic timed model.**  From an evaluation model and a latency per
operation: the response is ready `ℓ` after the operands and the control
clock (and the reveal clock, for an operation with a clear argument); a
clear response raises the reveal clock; a barrier raises the control clock. -/
def Model.timed {ι : Interface} (E : Model ι .ideal Id) (ℓ : ι.Op → Nat) : Model ι .timed Sched where
  step r := fun s =>
    let base := r.args.times.foldr max s.clock
    let base := if ι.pubArg r.op then max base s.revealed else base
    let t := base + ℓ r.op
    let (y, d) := (E.step ⟨r.op, r.args.untime⟩).run
    (((ι.cod r.op).retime t y, d),
     { clock := if ι.ctrl r.op then max s.clock s.revealed else s.clock,
       revealed := if (ι.cod r.op).hasClear then max s.revealed t else s.revealed })

/-- The timed model of a functionality at the given latencies. -/
def Functionality.timed (F : Functionality) (ℓ : F.ops.Op → Nat) : Model F.ops .timed Sched :=
  F.eval.timed ℓ

/-- The timed model of a hybrid at the given latencies. -/
def Hybrid.timed (fs : Hybrid) (ℓ : fs.ops.Op → Nat) : Model fs.ops .timed Sched :=
  fs.eval.timed ℓ

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

end Delay
end Weft
