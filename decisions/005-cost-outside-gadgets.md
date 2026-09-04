# 005 — Cost is not part of a gadget

## Choice
A gadget bundles circuit, assumptions, spec, good coins, allowed leakage
and the two proofs (correctness, simulatability). Cost is computed against
an MPC's cost model (`Gadget.cost`), and a bound is a separate theorem
about the pair (`Gadget.Priced`).

## Alternative
Gadget parameterised by a cost model with a `price` field and a `priced`
proof. Rejected: the same gadget then has to be restated per MPC.

## Reason
An invariant of the whole design: a circuit has semantics regardless of
the MPC (its `output` and `leak` follow from the `program` and `leak` of
the functionalities it calls, the same everywhere) but has a cost only
once an MPC is fixed (delay and communication need that MPC's latencies
and bandwidths). The same split holds one level up: a `Functionality` is
program and leak; an MPC is a price list over functionalities.
