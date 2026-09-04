# 012 — The adversary's view is the tagged trace

## Question
A simulator for a realised operation must produce the *concrete* view
of that operation's implementation from the *abstract* record. What does
it get to see, and what is a "view"?

## Choice
The view of a run is the list of records, one per request: the request's
public **kind** (which operation, e.g. linear / multiplication / reveal)
and what the functionality declares for it. `Model.tagged M kind` is the
model that leaks exactly that, and every compositional statement is about
`dist (M.tagged kind) c`.

`Realizes kσ kτ impl Mσ Mτ` says: for each request `o`, the concrete
tagged run of `impl o` equals "draw the abstract response, hand the
simulator the abstract record `(kτ o, Mτ.leak o y)`, pair the result".
The simulator sees the kind and the declared leak, never the request's
payload (in the ideal domain the payload *is* the secret) and never the
response unless the functionality leaks it.

## Why
1. The adversary knows the program and sees which operations the parties
   execute, so the kinds are part of its view in any honest model; making
   them explicit costs nothing.
2. Without the kind, a simulator given only the declared leak cannot tell
   a `mult` (declared leak `[]`, concrete view: a triple, two reveals of a
   uniform pair, linear ops) from a `lin` (declared leak `[]`, concrete
   view: one linear record). With the kind the simulator for `Std` on
   `Pre` is a three-way case split (`preHandler_realizes`).
3. Composition needs per-request boundaries in the concrete trace so that
   the next level's simulators can be applied record by record
   (`simList`). Flat leakage lists lose the boundaries; tagged records
   keep them, and `Realizes.comp` is then a two-line proof.

## Alternatives
* **A simulator indexed by the request itself.** Sound only if it is
  shown to depend on the request's public shape alone; not enforced by
  the type, so rejected as the definition.
* **A `kind` field on `Model`.** Equivalent, but it would put a
  presentation choice into every model; keeping `kind` beside the model
  in `Functionality` and in `Realizes` leaves `Model` as program and
  leak only.
* **Kinds encoded into the leak alphabet by convention.** Works, but
  every model would have to follow the convention; the tagged model does
  it once.

## Consequences
`Functionality` carries `K` and `kind`; sums tag kinds by side; a gadget
as a functionality has kind `Unit`. Top-level `Hiding` may still be stated
on the untagged model when the output is public and the kinds are
determined by it (the case for straight-line circuits).
