# 003 — An MPC is a price list; features are its support

## Choice
An MPC is one value, a list of `(capability, price)` pairs. `Has c M` is
list membership found by instance search. The cost function is derived
from the list, so "offered" means "finitely priced" by construction;
requests carry their `Has` evidence (with the price as data), so the cost
model reads prices off requests and never needs a lookup or decidable
equality on capabilities. Circuits state lower bounds (`[Has .mult M]`),
never a concrete MPC.

## Alternatives
1. **Open signatures with `Has τ σ` instances (data types à la carte).**
   The first design; still the substrate. Pro: open-world extensibility.
   Con: the feature set is implicit in typeclass constraints, not a
   value; nothing to compare, print or price.
2. **Cost function with an unbounded cost for unsupported operations.**
   Pro: one signature, availability as data. Con: typeclass resolution
   will not evaluate a function to discharge `Has`, so availability is
   not checked at the call site; `⊤` appears inside well-typed circuits.
3. **Capability classes per feature (`HasInv D σ`).** Kept, but as the
   mechanism for choosing between several realisations, not for
   describing an MPC.

## Why the price list
It is the one thing to pass around, the type checker enforces
availability, and adding a feature to the library or to an MPC never
touches existing circuits (circuits are lower bounds, absence is the
default, per-feature semantics is total).

## Trade
Closed world: the library owns the feature enumeration. An open variant
(features as name plus signature, `Has` by name) is possible at the cost
of exhaustiveness checks.
