# 014 — Public observations are explicit and never automatic

## Question
What does the adversary see of a run, and who decides?  The old
definitions answered in three places that did not agree: `Hiding` handed
the simulator the return value, so that at the ideal domain, where a share
is its value, `do reveal x; pure x` was provably hiding (report, Issue 1);
`kind` chose per theorem which part of a request the simulator saw, so
`payloadKind (mult x _) := x` certified an implementation that opened `x`
(Issue 2); and a model could return an opened value and leave it out of
the view (Issue 3).  Public inputs had no slot at all (Issue 8).

## Choice
The record of one request is fixed by the interface, structurally, and
nothing about a run is public unless it is in that record.

* A request is an **operation applied to operands**, and every operand
  has a **shape** (`Interface.dom : Op → List Shape`): a public input (a
  constant, a scalar, an opened value) is a `clear` operand, a secret
  input is a `share`.
* The response has a shape too (`Interface.cod : Op → Shape`), and
  `Shape.blank` keeps clear components and erases shares, on operands and
  response alike.  A functionality that takes or returns a value in the
  clear has published it, by shape, whatever its model says.
* A functionality's model is one **joint step**,
  `step : Req → m (Resp × disc op)`, whose second component is the
  declared disclosure, typed per operation (`Interface.leak`).  It may
  depend on the operands ("returns `[a·b]`, discloses `a − b`") and may
  be random and not a function of the response (the public coin of a
  random combination, `Examples/RandomCombination.lean`).
* The **event** of a request is `⟨op, blank y, leak⟩`, the **view** of a
  run is the list of events, and every privacy statement is about the
  joint distribution of output and view (decision 012).  The simulator's
  only input is the event.

There is no `kind`, no `Model.leak` accessor and no `Hiding`.  A share is
never compared, inspected or returned to the adversary by the framework;
it can only be passed to an operation, and the `program` command checks
that an implementation does nothing else (decision 015).

## Alternatives
* **Declared disclosure restricted to clear data**, so that a model could
  never mention operands (an earlier recording of Issue 1).  Rejected: it
  confuses leakage with output.  The disclosure is the trusted
  specification of what the functionality gives away; restricting it
  forbids honest functionalities.
* **A public alphabet `List Pub`** for the disclosure, with an encoding
  requirement on the values (the report's sketch).  Replaced by a type per
  operation: the disclosure of `randomCombination` is a field element, of
  a zero test a `Bool`, and nothing is gained by encoding either.  A
  common alphabet can be recovered by a map on events where two
  functionalities must be compared.
* **Tagging chosen per theorem** (`kind`), the old design.  Rejected for
  the vacuity route above and because tagging at the leaf and at the
  composition must agree for composition to be a theorem.

## Consequences
`Reveal` declares nothing: its response is clear by shape, and that is the
whole disclosure.  `openMul` realises the one-operation functionality
that returns `a·b` in the clear, whose simulator reads `a·b` off the
event; `do reveal x; pure x` does not realise the identity functionality,
because the event blanks the share while the view shows the value
(`Examples/Privacy.lean`).  Constants and scalars are clear operands,
`const : [clear F] → share F` and `smul : [clear F, share F] → share F`,
in the event by shape.

## Revisited (2026-09-05, later the same day)
The first form of this record put clear inputs in the operation's
constructor (`const (c : F)`, `smul (c : F)`) and kept operands shares
only, with a trusted `pubArg` flag telling the timed domain which
constructors carried a clear value.  Clear inputs are now operands with a
clear shape, the event records the blanked operands, and the flag is
gone: whether an operation consumes a clear value is
`Operands.hasClear (dom o)`.  Nothing else changed; the record of a
request is still structural and still the only public thing about it.
