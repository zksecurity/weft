# 009 — Statistical privacy

## Choice
Perfect privacy is the working notion. Statistical privacy is defined as
a total-variation bound on the Layer-0 `PMF` statement (008) and proved,
where possible, as "identical until bad": the perfect argument off a bad
event, plus a bound on the bad event's probability. Gadgets carry a
`Good` set of coins and, to be added, an explicit `ε`; sequential
composition adds the bounds.

## Alternatives
1. **Identical-until-bad as the definition**, with the bad event counted
   over coin prefixes of a fixed length. Constructive and composable by
   union bound, and a maximal coupling shows it loses nothing over a
   finite uniform space. Rejected as the *definition* for the same
   reasons as 008: prefix length is a stopping time under data-dependent
   control flow, and the bijection-based form inherits the count
   rigidity. Kept as the proof technique.
2. **Asymptotic ("negligible in κ").** Bookkeeping over 1 or the
   definition; state bounds as explicit functions of κ and never write
   "negligible" in a theorem.
3. **Distinguisher games.** Only for computational security, which the
   hybrid layer does not need; the base's computational security enters
   through UC composition outside the framework.

## Where it is needed first
Inversion by masking (`x·s` uniform only off `s = 0`), edaBit masking of
a bounded value by a longer random one (`ε = 2^(−κ)`), anything with a
rejection step.

## Open
Total variation on `PMF` is thin in Mathlib; the data-processing
inequality for `bind` (a contraction in TV) is the lemma that makes
statistical composition go through and will need to be developed.

## Revisited: no bad sets, an explicit `ε`, and perfect correctness

The `Good` set of coins is gone. Two things replace it.

* **Correctness is perfect.** A gadget's `correct` field says every output
  on the support of the run satisfies the spec. A gadget that needs an
  invertible mask asks the functionality for one: `randNZ`, a uniformly
  random nonzero share, is a feature with a price like any other
  (decision 011). Inversion by masking is then perfectly correct and
  perfectly hiding, and there is nothing to count.
* **The error is in privacy, as a number.** `ε` is total variation
  (`PMF.statDist`) between the real (output, reveals) and the simulated
  one; perfect gadgets carry `0`, and zero distance is equality
  (`PMF.eq_of_statDist_eq_zero`), so they prove an equation. Statistical
  realisations are `RealizesStat` with the same shape.

Counting tapes was rejected with the tape itself (008): a bad set of
coin prefixes needs a prefix length, which is a stopping time under
data-dependent control flow, and total variation is the quantity that
composes. What is still open is the composition lemma: `bind` is a
contraction in total variation, so `handle_realizes` holds up to the sum
of the per-call errors; that proof and the identical-until-bad technique
for establishing a single gadget's `ε` (the perfect argument off a bad
event, plus the event's probability) are the next items, needed first for
edaBit masking of a bounded value by a longer one.
