# 011 — Correctness is perfect; the functionality supplies invertible masks

## Question
Inversion by masking (`s ← rand; m ← reveal (x·s); s / m`) fails when the
mask is zero. Where does that failure live: in correctness, in privacy,
or in the functionality?

## Choice
Correctness is perfect: a gadget's `correct` field states that *every*
output on the support of its run satisfies the spec. A gadget that needs
an invertible mask asks the functionality for one. `RandNZ` (`randNZ`,
uniform on the nonzero elements) is a feature with an ideal model and a
price, like `Rand`, and the inversion gadget uses it. Then `x·s` is a
uniform nonzero element for `x ≠ 0`, the output is `x⁻¹` with
certainty, and the proofs are the perfect ones (`invertGadget`,
`invert_correct`, `invert_dist`).

The statistical error, when there is one, lives in privacy only, as the
gadget's `ε` (decision 009).

## Alternatives
1. **A `Good` set of coins with a counting bound**, on which the gadget
   behaves; composition intersects the sets and unions the bounds.
   Rejected: it ties correctness to a probability, makes every caller
   carry a failure probability it did not ask for, and needs the tape to
   count on (decision 008).
2. **Correctness with probability `1 − ε`** stated on `PMF`. Deferred:
   nothing in the current gadgets needs it once masks are nonzero, and it
   would complicate every composition theorem with a second error term.
   It can be added later as a separate field without changing the
   perfect notion, which stays the default.
3. **Rejection sampling inside the circuit** (`s ← rand`, retry while
   `s·t = 0` for a second random `t`). This is how `randNZ` is
   *realised* on many MPCs, and it belongs in a handler for `RandNZ`
   priced by that MPC, not in every circuit that wants a nonzero mask.

## Consequences
`MPC` price lists gain a `randNZ` entry where offered. `Feature.ideal`
needs `Nontrivial F` and `DecidableEq F` for the nonzero subtype. The
evaluation models give `randNZ` a dummy value like `rand`; values under
evaluation models are meaningless by design.
