# 018 — Public values and control flow in the timed domain (open)

**Status: open.**  This record lays out the design space; no choice has
been made.  It exists because the current mechanism (two global clocks
and a `Barrier` functionality, decisions 002 and 017) is a patch, and
the author asked whether a better design exists.

## The question

Delay is the longest path through the dependency hypergraph of a run:
nodes are requests, a hyperedge goes from the operands of a request to
its response, weights are latencies (decision 002).  Three kinds of
dependency feed that graph:

1. **share → operation.**  A share carries its ready time in the timed
   domain.  Tracked exactly.
2. **opened value → operation, through clear computation.**  An opened
   value is a plain Lean value (`reveal : share F → F`), so it carries no
   time, and whatever is computed from it is untimed too.  Today the
   *reveal clock* stands in for it: an operation with a clear operand
   waits for the latest opening, whichever it was.  An over-approximation
   with global state.
3. **opened value → which operation is issued next** (control).  A
   program branches with a Lean `if` on a plain value, which the
   interpreter cannot see; the operations in the taken branch have
   operands that were ready long before, so the tracker issues them too
   early.  Today the program must say `barrier`, which raises the
   *control clock* to the reveal clock.  A trusted annotation; forgetting
   it under-counts.

An example of 3.  Real execution: `c` is known at the end of round 1, the
multiplication is issued in round 2, `y` is ready at round 2.

    c ← reveal x            -- opened at round 1
    if c = 0 then
      y ← mul a b           -- a, b ready at round 0
    else
      y ← mul a d

The tracker sees `mul a b` with operands ready at 0 and no operand that
mentions `c`, and reports `y` at round 1.  The oblivious version
`y ← smul c ab + smul (1 - c) ad` really is ready at round 1, because
there the choice is data and `c` is an operand; the branching version
costs a round more, because the parties must *learn* `c` before choosing.
The missing edge is `c → mul`, an edge from an opened value to a gate
that does not take it as an operand.

Both patches have the same root cause: **opened values are plain Lean
values**.  Every design below is a way of not letting them be.

## What other systems do

* **MP-SPDZ** minimises rounds exactly as we do, by a longest-path
  merge over a dependency graph, but "only within a basic block": a
  branch or loop on a run-time public value (`@if_`, `@for_range`) ends
  the block, and a plain Python `if` cannot branch on a run-time value
  at all, so every control dependency is a forced synchronisation point
  (Keller, *MP-SPDZ: A Versatile Framework for Multi-Party Computation*;
  the compiler's `optimization` page).
* **MPyC** represents every secure value, and every opened value, as an
  `asyncio` future; arithmetic on futures is scheduled by data
  dependencies, and looking at an opened value requires `await`, which
  synchronises the program with it.
* **Haxl** (Marlow et al., *There is no Fork*, ICFP 2014): data fetches
  are batched into rounds; independent fetches combined applicatively
  share a round, a monadic bind on a fetched value starts a new round;
  `ApplicativeDo` recovers the applicative structure from `do`-notation.
* **Selective applicative functors** (Mokhov et al., ICFP 2019): all
  branches are declared statically and one is selected dynamically, so
  a static analysis can over- and under-approximate the effects of a
  program with conditionals.
* **Guarded type theory and synchronous languages**: the *later*
  modality `▷ T` types data available one tick from now; clocked type
  theory indexes it by a clock; Lustre's clock calculus makes a stream's
  availability part of its type and rejects combining streams of
  different clocks without `when`/`merge`.
* The MPC languages with a formal semantics (Wysteria, Symphony,
  Viaduct) fix *who* computes and *who sees what*; none gives a round
  cost semantics.

Three independent systems that count rounds at run time (MP-SPDZ, MPyC,
Haxl) converge on one shape: **values are futures, data flow through
futures is tracked automatically, and inspecting a future is an explicit
synchronisation.**

## Options

### O1. Keep dependency tracking, drop `Barrier`

Delay counts data dependencies only; the reveal clock stays for clear
operands; control dependencies are not counted.  Simplest change; delay
under-counts for every program that branches on an opened value
(`binarySearch` in the gallery: 4 rounds instead of 12).  Still one
global clock.  Not an upper bound.

### O2. Opened values are timed; inspecting one is a program primitive

A domain interprets clear values as well as shares: `Domain ⟨sh, cl⟩`,
with `cl T = T` in the ideal and erased domains and `cl T = Timed T` in
the timed one.  `reveal` returns `D.cl F`; a clear operand carries its
own time, so `smul e b` is ready at `max e.time b.time`, a plain data
edge, and the reveal clock disappears.  Clear computation goes through
`Applicative D.cl` (`Timed` combines by max), with `Mul (D.cl F)` and
friends derived so that `const (e * d)` reads as today.  The one way to
turn a `D.cl T` into a `T` is a constructor of the program,

    look : D.cl T → (T → Prog ι D α) → Prog ι D α

which the ideal semantics interprets as application and the timed model
as "advance *now* to `c.time`".  There is then a single piece of
scheduling state, `now`, the time at which the program is issuing
requests; an operation starts at the max of `now` and its operands'
times; `delayOn` is the max of `now` and the output's time, which also
closes the report's `pure`-selection gap.  Nothing can be forgotten: a
program cannot branch on an opened value without `look`, and the
events of the timed run record timed clear operands (`Event ι D`, with
`D.erase := ⟨fun _ => Unit, D.cl⟩`), so no extraction from `D.cl`
exists outside `look`.  This is MP-SPDZ's basic block, MPyC's `await`
and Haxl's round boundary, in the free monad.

Cost: a constructor in `Prog` (a case in every induction: `run_bind`,
`handle_realizes`, `cost_handle`, `Valid`, `runOut_timed`), a `look`
field on `Model`, `Applicative` instances for the domains, and a
functorial spelling of clear computation in the few programs that do
more than arithmetic on opened values (`bitsOf` in the conversions).
About a day and a half.

### O3. Opened values are timed and cannot be inspected at all

O2 without `look`.  An opened value can be an operand or be combined
with other clear values, never branched on.  There is no scheduling
state whatsoever: the timed model is a pure function of the request,
and delay is exactly the longest path of the hypergraph.  What is
given up is public control flow on opened values: rejection-sampling
loops, early termination, abort-on-check, binary search on opened
comparisons.  Everything in the examples except `binarySearch` is in
this fragment, and O3 is precisely the `look`-free fragment of O2, in
which `now` is never advanced.

### O4. A countdown on values

The author's suggestion: a clear value resolves after `n` steps.  This
is O2/O3 in relative coordinates: a countdown is `ready − now`, and it
has to be recomputed as `now` advances, whereas an absolute ready time
is fixed once and combined by `max`.  Same design, less convenient
representation.  At the *type* level it becomes O5.

### O5. Rounds in the types

The later modality: `▷ⁿ T` is a value available `n` ticks from now, a
program is indexed by its current round, `reveal` returns `▷ T`, and
using a value too early is a type error unless the program `await`s
it.  Round complexity becomes a typing judgement, compositional and
static, with no evaluation.  Against it: latencies belong to the MPC
(decision 017), so the indices would be symbolic in the price list and
the type of a program would mention its MPC; and a branch on an opened
value makes the index value-dependent.  Elegant for straight-line
programs, heavy for the library's purpose, which is to *compute* a
number for a program written once.

### O6. Static structure: selective functors or a reified graph

A free selective functor declares every branch statically and selects
one at run time, so worst-case rounds over all branches can be read off
without running; a deep embedding with named wires does the same.
Either replaces the free monad, loses `do`-notation over Lean's own
`List.mapM` and recursion, and undoes decision 001.  Noted because O2's
`look` gives the same information dynamically: both continuations of a
`look` on a `Bool` are available to an analysis that wants a worst case.

## Comparison

| | annotations | global state | exact for straight-line | counts control edges | change |
|---|---|---|---|---|---|
| today | `barrier` | two clocks | over-approximates clear operands | if annotated | — |
| O1 | none | reveal clock | over-approximates | no | small |
| O2 | none | `now` | exact | yes, structurally | large |
| O3 | none | none | exact | not expressible | large minus `look` |
| O5 | types | none | exact, static | value-dependent types | rewrite |
| O6 | none | none | exact, static | yes | rewrite |

## Leaning

O2, with O3 as its `look`-free fragment.  It is the design three
production systems arrived at independently, it is the only one that
is both exact and complete without annotations, and it makes the
scheduling state one number with an obvious meaning.  If public control
flow on opened values is judged out of scope, O3 is O2 without one
constructor and one field, and can be chosen later by deleting them.

## References

* Marcel Keller, *MP-SPDZ: A Versatile Framework for Multi-Party
  Computation*, CCS 2020; MP-SPDZ documentation, *Compiler
  Optimizations*.
* MPyC, *Multiparty Computation in Python*, runtime documentation.
* Simon Marlow et al., *There is no Fork: an Abstraction for Efficient,
  Concurrent, and Concise Data Access*, ICFP 2014; *Desugaring Haskell's
  do-Notation into Applicative Operations*, Haskell 2016.
* Andrey Mokhov et al., *Selective Applicative Functors*, ICFP 2019.
* Bahr, Grathwohl, Møgelberg, *The Clocks Are Ticking: No More Delays!*
  (clocked type theory); Guatto, *A Generalized Modality for Recursion*.
* Rastogi et al., *Wysteria*; Darais et al., *Symphony*; Acay et al.,
  *Viaduct*.
