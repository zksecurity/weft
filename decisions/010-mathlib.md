# 010 — Build on Mathlib

## Choice
Mathlib is a dependency. Use its definitions wherever one exists: `Field`
and `ZMod` for fields, `Equiv` for re-randomisations, `PMF` and
`uniformOfFintype` for distributions, `AddCommGroup` for additive
masking; `ring` and `field_simp` close the algebra.

## Alternative
A Mathlib-free sketch with stand-in classes. Used for the first
iterations; rejected as soon as proofs beyond evaluation were needed
(the Beaver identity, inversion correctness) and because textbook
privacy definitions live on `PMF`.

## Conversions done
`Concrete` in the multi-field file replaced by Mathlib's `CommRing`
(`Field`/`Inv` where inversion is used), an `LT` for `cmp`, and
`Encodable` for the shared `ℕ` coin and leak alphabet, with `ZMod n`
instances through `ZMod.val` and `Nat.cast` (Mathlib has no order on
`ZMod`, rightly; the ideal model orders by canonical representative).
`Fin 2` is `ZMod 2`; unbounded costs are `WithTop`; edaBit vectors are
`Fin m → ⟦ZMod 2⟧` with `Fin.cons`/`Fin.tail`; prefix counting is
`Finset.card`. Example fields are `ZMod 7`, `ZMod 16`, `ZMod 17`.

## Found by the conversion
`decide` on `ZMod 17` refuted the toy A2B under a mask larger than the
input: the sketch omits the edaBit protocol's modular correction, so its
correctness assumption is `r ≤ x`. Recorded in the file; the real gadget
adds a binary compare-and-subtract of `p`.
