# Weft : Verifying MPC Programs in Lean

A library for writing MPC programs against ideal functionalities and proving, in Lean 4 on Mathlib, that:

- They are correct
- What they cost in rounds and communication
- That they are private

With easy composition of subcircuits / subprograms based on ideas from the universal composability framework.

## Documentation

Start with [Universal Composability](docs/00-universal-composability.md),
then read [Functionalities](docs/01-functionalities.md),
[Hybrids](docs/02-hybrids.md), [Programs](docs/03-programs.md),
[Privacy](docs/04-privacy.md), [Rounds](docs/05-rounds.md),
and [Communication](docs/06-communication.md).

## Building

```
lake exe cache get   # Mathlib's cache, once
lake build           # the library and the examples
```
