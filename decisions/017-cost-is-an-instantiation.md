# 017 — Cost is an instantiation of the hybrid, never a property of a functionality

## Question
Where do delay and communication live?  The first version of the library
gave `Functionality` a `timed` field, a timed model of its interface at
given latencies, and the timing example modelled one compound operation
as two functionalities that differed only in that field.  The author's
objection (2026-09-05): a functionality captures behaviour, nothing
else; propagation delay and communication cost are not a functionality
thing.

## Choice
A functionality is `⟨ops, eval, IsModel, isModel_unique⟩`, behaviour
only.  Cost appears when a hybrid is *instantiated* in a cost model: a
model of each interface in the scheduling monad `Sched`, whose state is
the two clocks and a communication counter.  Such a model does the
behaviour (it computes the same values as `eval`) and something more: it
stamps each response with the round at which it is ready, so that the
delay of a program is the longest path through its dependency
hypergraph, and it adds the operation's communication to the counter.
Both are read off one scheduled run (`delayOn`, `commOn`).

An MPC is a list of such instantiations, `(F : Functionality) × Model
F.ops .timed Sched`.  One generic timed model, `Model.timed`, instantiates
any interface from its evaluation model, a price per operation and the
interface's scheduling metadata; a functionality at a price is an entry
(`(Mult F).priced ⟨1, 2⟩`), and any other timed model of the interface
may be used instead (`MPC.entry`, a per-input profile for instance).

The exact instantiation of an abstract operation under a realisation is
to run the implementation in the target's cost model
(`Realization.timed`, `MPC.derived`).  A scheduled run of a caller with
every abstract operation instantiated that way is the scheduled run of
the inlined program, output, clocks and counter alike
(`Realizations.runOut_timed`); delay and communication of a program
written against abstract operations are computed once, in the hybrid,
and are what the instantiated program costs.  Atomic and profiled models
of an abstract operation are approximations of the derived one.

## Alternatives
* **A timed model per functionality** (the first version).  Rejected:
  it makes cost a property of behaviour, forces one functionality per
  cost model, and puts the profile of a compound operation on the wrong
  side of the line.
* **A hand-written timed model per standard interface**, beside the
  functionality, so that evaluation stays fast: the first form of this
  decision.  Dropped once the generic model, written without `let`
  bindings, proved linear in the kernel (a chain of forty
  multiplications in a few seconds); hand-written models remain for what
  the generic one cannot express, such as a per-input profile.
* **A typeclass supplying the timed model of an interface.**  Rejected
  as a canonical cost per functionality in disguise.  The MPC names the
  instantiation it uses.
* **Communication as an additive cost model only**, accumulated by the
  interpreter's trace from a price per operation.  Kept for the
  ideal-domain, distributional statement (`costDist`, `cost_handle`), but
  it cannot express the derived instantiation, whose communication
  depends on the run; the counter in the scheduling state can.
* **Dropping the `MPC` list** and writing cost models per hybrid by
  hand.  Possible, and nothing semantic depends on the list; it is kept
  as the convenient way to build a cost model of a hybrid from
  instantiations of its parts.

## Consequences
`Functionality.timed`, `Hybrid.timed`, `MPC.price` and `MPC.comm` are
gone; `Price` moves to `Weft.Timed`, `MPC` to its own module, and
`Std.mpc`/`Pre.mpc` are the black box and the preprocessing model as
MPCs at default prices.  `Examples/Timing.lean` has one `MulAdd` and
three MPCs for it.  What remains open is the bound a hand-written model
gives when it dominates the derived one: it needs monotonicity of the
interpreter in the scheduling state, which holds only for domain-generic
callers, a hypothesis Lean cannot state about a program at the timed
domain (report, Issue 10, for why profiles are not exact).
