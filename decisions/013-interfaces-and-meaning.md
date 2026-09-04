# 013 — Signatures are interfaces; meaning is fixed per name

## Question
`Has (MulTriple D) σ` (formerly `Triple`) says only that the request `get : D.S × D.S × D.S` is
available; it is not a functionality. When does a circuit have
semantics, and who fixes the distribution behind "triple"?

## Choice
Three layers, each with one job.

1. **Signature = interface.** A `Sig` is a vocabulary of requests with
   their response types; `Has τ σ` is interface inclusion; `Circ σ α` is
   syntax. A circuit's type states the interfaces it uses and nothing
   about their meaning. Interfaces are named after the functionality
   they belong to (`MulTriple`, `SquarePair`, `DoubleSharing`), because
   the name is the promise, and two correlations with the same shape
   must be distinct interfaces.
2. **Functionality = interface + one ideal model.** The library fixes
   one ideal model per interface name (`MulTriple.ideal`, `Mult.ideal`, …),
   and on the price-list route binds it by name (`Feature.ideal`), so a
   circuit over a price list has its semantics the moment it typechecks.
   An MPC prices interfaces; it cannot redefine them.
3. **Interpretation = any model of the interface**, a parameter of
   `run`: the ideal `PMF` model for privacy, `Id` for evaluation, the
   clock model for delay, hybrids with abstract callees, wrong models for
   counterexamples. Theorems always name the model.

Consequently a circuit has semantics as soon as its interfaces have
their ideal models, i.e. always on the price-list route and as soon as a
model is named in the core; it never waits for an MPC or a realisation.
Realisation (a protocol, or a circuit over other features) is the UC
step and does not touch semantics.

## Alternatives
* **`Has` indexed by functionalities in the core**, so that even core
  circuit types carry the canonical model. Compatible with the above
  (it is a wrapper over `Functionality`), and worth adding if core
  circuits are to be user-facing; the feature-name route already is
  this for price lists. Not done yet.
* **Models inside signatures** (a request carries its distribution).
  Rejected: the same syntax must be interpreted in several monads and
  against hybrid and counterexample models, and the request's payload in
  the ideal domain is the secret, which no model should have to mention.

## Consequences
Done: shape-named interfaces are renamed (`Triple` → `MulTriple`,
`Square` → `SquarePair`, `Double` → `DoubleSharing`), each is its own
inductive rather than an abbreviation of a generic `Get D T` (which is
gone), and `Correlation` remains the generic way to model any of them.
The counterexample in `Beaver.lean` is now explicitly a *wrong model* of
the `MulTriple` interface, which is the only way it can be stated.
