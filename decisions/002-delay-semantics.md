# 002 — Delay by dependency tracking, not explicit parallel nodes

## Choice
Delay (the latency notion; rounds are its unit) is computed in the *timed
domain*: every value carries the round at which it is available and an
operation's result is ready at `max(inputs) + latency`. Abstract
operations carry a *timing profile* (delay from each input to the output)
so that composition is exact. Sequential `do`-code gets the parallel
count; nothing is marked parallel. The `par` node remains available for
pinning a schedule but is not needed.

## Alternatives
1. **Explicit parallel node with `seq ↦ +`, `par ↦ max`.** The first
   design. Pro: the round count is that of the schedule the programmer
   wrote. Con: the programmer must write the schedule; independent
   operations written sequentially are over-counted; composition of
   delay through realisations is exact only if abstract operations are
   atomic, otherwise an upper bound.
2. **Automatic ASAP scheduler as a circuit transformation.** Pro: keeps
   one semantics. Con: needs an inspectable circuit (001) or a symbolic
   run; a verified transformation is more work than a second domain.

## Why dependency tracking
It is what the protocol will actually do under eager scheduling, it
needs no annotations, it is the same interpreter on another domain, and
with profiles it composes exactly along realisations (the longest path
through a substituted dependency graph decomposes at the boundary).

## Known gap
Control dependencies: an `if` on a revealed value whose branch does not
data-depend on it is not seen. Fix: a clock in the interpreter raised by
every reveal, so operations issued after a reveal are timed no earlier
than it. Conservative, one line, not yet done.

## Revisited: `par` dropped
`Circ` is now a plain free monad (`pure`, `call`). Every parallel construct
in the examples became sequential `do`-code with the same delay by
evaluation. The explicit-schedule cost algebras (`seq +`, `par max`) are
gone; `Resource` is for additive costs only and delay is the timed domain.

Two rules were needed to make the timed domain honest, both found by
evaluation during the change:

* **Reveal does not raise the clock.** A first version serialised every
  operation after a reveal, which turned Beaver's two independent reveals
  into two rounds. Instead the interpreter keeps a *reveal clock* (the
  latest reveal so far) and a *control clock*. Operations with a clear
  argument (`const`, `smul`) are timed no earlier than the reveal clock,
  because clear computation is opaque and may depend on anything revealed.
  A `barrier` feature, placed where a circuit branches on revealed values,
  raises the control clock to the reveal clock; everything issued after it
  waits. Straight-line code never needs a barrier, and forgetting one
  under-counts delay only (never affects semantics or privacy).
* **Clear values stay plain.** Timing clear values too would have made a
  generic circuit's `if bit = 0` compare times; `binarySearch` would have
  taken the wrong branch. Only shares carry a time.

Evaluation also corrected two of my expected numbers: a sorting network's
outer outputs finish a layer earlier than its middle ones, and the A2B
adder's last bit needs three carries, not four (the fourth AND only feeds
the unused carry-out). Both are what a real scheduler would report.
