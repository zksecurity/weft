# 006 — Functionalities and realisations as one notion

## Choice
A functionality is an interface with a `program` and a `leak`. A
realisation of `F` over `G` is a handler (`F`'s operations as circuits
over `G`) with a `Realizes` proof (correct program, reveals simulatable
given the declared leak). Identity is trust (the MPC provides `F`),
composition is inlining, feature inclusion and sums are realisations. A
circuit with a spec and declared leak is a one-operation functionality
realised over its signature; a gadget is that plus assumptions.

## Alternatives
1. **Primitives and circuits as different kinds.** The first framing.
   Con: an AES functionality provided natively and an AES circuit would
   be unrelated objects; callers could not be written once against
   "AES".
2. **Circuits composed only by inlining, proofs by the sequential lemmas.**
   Still available (direct calls); insufficient for swappable
   implementations and for stating the trusted base.

## Reason
UC's hybrid model, made literal: a protocol is proved against its own
specification in the hybrid with abstract sub-functionalities, and any
later realisation of those composes in (`Realization.comp`) with no
re-proof. The trusted base is the set of identity realisations, i.e. the
price list. Cost composes the same way (`cost_handle`, derived prices).

## Subtlety recorded
"X given Y" is not transitive; the compositional statements are about the
joint view, which is why `handle_private` gives reveals given (abstract
reveals, output) and `Hiding.transport` composes joint statements.
