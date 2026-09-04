# Glean — verifying MPC circuits in Lean 4

A framework, at the design stage, for formally verifying MPC circuits
against ideal functionalities in Lean 4 on Mathlib. Working name; see
`DESIGN.md` §10 for alternatives.

* `DESIGN.md` — the design as it stands.
* `decisions/` — one record per design choice: alternatives considered and why one won.

## Lean sketch

Builds with `lake build` (Lean 4.29, Mathlib; fetch the cache with `lake exe cache get`).
Definitions and examples are real; the compositional theorems are stated with `sorry`.

* `Glean.lean` — the core: signatures, the free monad of circuits (no parallel node), domains, features, coins, the interpreter with its reveal and control clocks, the timed domain for delay, hiding, ideal models, examples.
* `Gallery.lean` — ten circuits in different styles (parallel, sequential, reactive, masked, records, feature-dispatching), theorems closed by evaluation.
* `Features.lean` — an MPC as a price list: feature sets in the circuit type, subtyping by widening, costs derived so that offered means finite.
* `FieldCirc.lean` — circuits that need `Field D.F`: interpolation (zero delay) and inversion by masking.
* `MultiField.lean` — circuits generic over field types, MPCs pricing features per field, switching between fields, edaBits and A2B conversion.
* `Timing.lean` — delay by dependency tracking: values carry their ready time, sequential `do`-code gets the parallel count, timing profiles make composition exact.
* `Gadget.lean` — Clean-style gadgets: a circuit with assumptions, spec, allowed leakage and good coins; cost computed per MPC; composition discharges assumptions from specs.
* `Privacy.lean` — simulation-based privacy: "X can be simulated given Y" for projections of a run, the mask-explanation lemma, statistical variants, and the `PMF` definitions.
* `Compose.lean` — a verified circuit as a functionality; the composition theorem.
* `Functionality.lean` — functionalities and realisations as one notion; AES over the black box as the example.
* `AesHybrid.lean` — a protocol in the AES-hybrid, an AES circuit with its realisation proof, and the instantiation that removes the AES operation from the hybrid.
* `Cost.lean` — delay and communication as separate observables; the composition theorems for cost.
* `Silent.lean` — over add and mul alone, every circuit is hiding (proved).
