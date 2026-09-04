# 007 — Semantics by domain polymorphism: ideal, timed, symbolic

## Choice
Circuits are polymorphic in the domain (the share type). The same circuit
is run in the *ideal* domain (a share is its value) for semantics and
privacy, in the *timed* domain (values carry ready times) for delay, and,
planned, in a *symbolic* domain (values are polynomials in inputs and
coins) for an automatic privacy check of the masking pattern.

## Alternatives
1. **Instrumented interpreter** (cost accumulators inside `run`). Kept
   for communication and for the explicit-schedule delay; but latency
   by dependency needs per-value information, which only a domain gives.
2. **Syntactic analyses** over an inspectable circuit (001, alt. 1).

## Reason
Polymorphism in the domain is what prevents circuits from looking inside
shares; it turns out to also be the cheapest way to get several
semantics from one program with nothing added to the language. Each new
analysis is a new domain plus a per-feature model, and correctness of an
analysis is a theorem relating two domains.
