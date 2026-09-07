# Universal Composability

We want to prove an MPC program once, against the operations it needs.
A multiplication may be provided by an arithmetic black box or implemented using Beaver triples;
callers should depend on the multiplication specification, and the implementation should discharge that specification.

Universal composability gives this way of organising cryptographic proofs: specify a task by an *ideal functionality*, prove that a protocol realises it, and substitute that protocol into larger constructions.
The security definition accounts for the surrounding execution, so a component's guarantee survives composition.
See Canetti's [Universally Composable Security](https://eprint.iacr.org/2000/067) for the general framework.

## The Hybrid Model

An MPC program in Weft runs against a *hybrid*: a collection of ideal functionalities.
These supply operations such as multiplication, opening, and correlated randomness.
The program passes shares between operations and computes on values returned in the clear.

The ideal functionalities are assumptions.
Weft does not represent the parties, their local shares, or the messages implementing a primitive.
We prove properties of the program given the specified behaviour of its primitives.
A functionality implemented by another Weft program can then be replaced by that implementation and its own assumptions.

For example, `Std F` supplies linear arithmetic, multiplication, and opening.
`Pre F` supplies linear arithmetic, opening, and Beaver triples.
The certificate `beaverMult` realises multiplication over `Pre F`.
Together with the two inclusion realisations, it gives `stdOverPre : Realizations (Std F) (Pre F)`.
Hence a caller proved over `Std F` can be instantiated over `Pre F` by inlining those realisations.
The construction is in [Examples/Privacy.lean](../Examples/Privacy.lean).

## What the Simulator Must Reproduce

The adversary sees an event for every request: its operation, clear operands, clear response components, and declared disclosure.
Shared components are erased;
public structure, including list lengths, remains.

A realisation consists of an implementation and a simulator.
The simulator receives the ideal functionality's event and produces the implementation's view.
The required equality is on the *joint distribution of output and view*.
Matching the view alone is insufficient: a returned share may be opened by the next caller, revealing its correlation with the view.

`handle_realizes` proves that replacing the operations of a valid caller preserves this joint law, with each abstract event expanded by its simulator.
`output_transport` gives equality of output distributions;
`Realization.comp` packages the resulting implementation and simulation proof into another certificate.
Preconditions are carried through the composition.
The definitions are in [Weft/Realization.lean](../Weft/Realization.lean).

## What Weft Proves

The formal model uses stateless ideal `PMF` kernels and terminating programs.
Perfect realisations preserve the joint distribution exactly;
statistical realisations retain an exact output marginal and bound the joint simulation error.
Costs are specified separately by an instantiation of the hybrid.

The composition theorem is about this model.
Weft does not formalise a general interactive UC execution or certify simulator efficiency.
Transferring a hybrid proof to computationally secure implementations requires an interactive embedding and appropriate efficient simulators;
those arguments are external to the library.
Sessions, hidden persistent state, and amortised preprocessing also require a different functionality model.

## Reference

1. [Functionalities](01-functionalities.md): interfaces and their meaning.
2. [Hybrids](02-hybrids.md): the functionalities available to a program.
3. [Programs](03-programs.md): requests, public computation, and interpretation.
4. [Privacy](04-privacy.md): how to realise a functionality and compose proofs.
5. [Rounds](05-rounds.md): data dependencies, control dependencies, and delay.
6. [Communication](06-communication.md): prices, accumulation, and cost distributions.

[Next: Functionalities](01-functionalities.md)
