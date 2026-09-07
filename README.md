# Weft : Verifying MPC Programs in Lean

A library for writing MPC programs against ideal functionalities and proving, 
in Lean 4 on Mathlib, that:

- They are correct
- What they cost in rounds and communication
- That they are private

With easy composition of subcircuits / subprograms based on ideas from the universal composability framework.

## Building

```
lake exe cache get   # Mathlib's cache, once
lake build           # the library and the examples
```
