# 008 — Privacy definition and proof method

## Question
Is reasoning about sets of coin tapes the cleanest way to prove privacy,
and does it compose? The candidates, compared on definitional clarity,
per-gadget effort, composition effort, automation, evaluation by `rfl`,
statistical security and Mathlib fit. An independent review was obtained
from a reviewer given only a self-contained brief; its findings are
folded in below and marked.

## Candidates

**A. Coin tape and bijections (couplings).** Coins are a tape `Nat → R`
with a next-unread index threaded through the run. Privacy: a simulator
and, per input, a bijection `π` on tapes such that the real pair
`(Y, X)` equals the ideal pair pointwise after re-randomisation, with
simulator coins taken from a disjoint half of `π ω`.
- Pro: first-order, constructive, evaluation by `rfl`; each gadget proof
  is "set the mask to the value that explains the reveal".
- Con (composition): the continuation's coin segment starts at an offset
  that is a value-dependent stopping time; the second step's bijection is
  fibred over the first's outcome; the composed simulator must re-thread
  per-call leaks in trace order. It composes, but the bookkeeping is the
  ugliest part of the design.
- Con (soundness, from the review, confirmed): an arbitrary bijection on
  an *infinite* tape is not measure-preserving. A Cantor-style bijection
  of `Bool^ℕ` can map an event of probability 1/4 onto one of
  probability 1/2, so the pointwise clause can hold while the
  distributions differ. As a *definition* the bijection must be on a
  finite prefix `R^n` with the tail fixed, at which point it is finite
  counting in disguise.
- Con (rigidity, from the review): a bijection `R^n ≃ R^m × R^k` forces
  the real coin count to equal the ideal count plus the simulator's, so
  simulators get padded to make counts match.

**B. `PMF` semantics.** `run : Circ → PMF (output × leaks)` with `rand`
as `uniformOfFintype`. Perfect privacy is equality of `PMF`s, jointly
with the output; statistical is a total-variation bound.
- Pro: the textbook definition (Lindell, "How to simulate it"); Mathlib
  supplies `PMF`, `bind`, `map`, `uniformOfFintype`, `Equiv`; composition
  is bind-congruence plus induction, with no offsets or padding, and
  independence of simulator coins is automatic from a fresh `bind`.
- Con: noncomputable, so no evaluation by `rfl`; raw `ENNReal` sums are
  tedious; total variation on `PMF` is thin in Mathlib.

**C. A small relational logic over `PMF`** (pRHL/EasyCrypt style): B's
definition with A's technique as inference rules, chiefly a sampling rule
"uniform mapped through a bijection is uniform" and a bind rule.
- Pro: per-gadget proofs stay one mask lemma; composition stays B's.
  Haagh, Karbyshev, Oechsner, Spitters and Strub (2018) did MPC over an
  ABB this way in EasyCrypt and report the mask lemma does almost all
  the work.

**D. Symbolic checker** (maskVerif, λ_obliv, Pettai–Laud): run the
circuit in a symbolic domain where values are polynomials in inputs and
coins; a reveal is safe if it is a secret expression plus a fresh coin
used nowhere else. A certified decision procedure, sound against B.
- Limitation: data-independent control flow and the masking pattern only.

**E. Tree-shaped (splittable) tapes**: `bind` splits the tape so each
sub-circuit gets a structurally addressed fresh segment.
- Removes A's offsets and makes couplings componentwise; does not remove
  count rigidity; makes statistical bad-sets awkward. A good evaluation
  semantics, not a good definition.

**F.** Conditional-independence definitions; SSProve-style packages.
Heavier than an ABB-hybrid needs; not pursued.

## Choice: layered
- **Definition (Layer 0): B.** `runP : Circ → PMF (output × leaks)`;
  `C` realises `F` with simulator `Sim` iff
  `runP C = do (y, ℓ) ← runP_F; s ← Sim ℓ; pure (y, s)`. Conditioning is
  on `F`'s *leak*, never on the output: a sub-gadget's output is a hidden
  handle that nobody sees, so "simulatable given output" does not
  compose; the top-level "given output" case is subsumed when the output
  is revealed (review finding; `Realizes.private_` already conditions on
  the abstract leak).
- **Evaluation (Layer 1): computable tape semantics** with an adequacy
  lemma `PMF.map (runT C) uniform = runP C`, proved once by induction.
  Tree tapes (E) keep that induction offset-free. Concrete circuits keep
  evaluating by `rfl`/`decide`. A computable finitely supported `ℚ≥0`
  distribution as the carrier, with a coercion to `PMF`, is worth trying
  so that small gadgets close by `decide` (review suggestion).
- **Proof rules (Layer 2): C.** Two lemmas carry the library:
  L1, `PMF.map e (uniformOfFintype α) = uniformOfFintype α` for
  `e : α ≃ α`, with the corollary "`do r ← U; pure (s, r + s)` equals
  `do r ← U; pure (s, r)`" (explain the mask); L2, the writer-over-`PMF`
  bind lemma `runP (c >>= k) = runP c >>= fun (y, ℓ) => map (ℓ ++ ·) (runP (k y))`.
- **Composition (Layer 3):** if `G` realises `F` then substituting `G`
  into a caller `C` proved in the `F`-hybrid realises `C`'s functionality,
  with `Sim = Sim_C ∘ per-call Sim_G`; induction on the free monad, one
  bind re-association per operation node. Opaque continuations are
  harmless: the `call` case gives an induction hypothesis for every
  continuation value.
- **Automation (Layer 4): D**, later, for the masking pattern.

## What changes in the sketch
`Rerand R := Tape R ≃ Tape R` is demoted from definition to a proof
device, and only bijections on finite prefixes are admissible; `SimFrom`
on tapes is the Layer-1 form, `SimFromPMF` is the definition. `Hiding'`
(given output) is a convenience for top-level circuits, not the
compositional notion.

## Order of work
L2 first (nothing goes through without it), then L1, then the Layer-3
theorem, then adequacy. VCVio (Devon Tuma, Lean 4), a `PMF`-backed
oracle-computation monad, should be examined before building Layer 0
from scratch.

## Revisited: no tape at all

The layering above kept a computable tape semantics as Layer 1, with a
bijection on finite prefixes as a proof device and an adequacy lemma to
the `PMF` definition. On implementation both were dropped; the
definition is the only semantics.

**Why the tape bijection is not needed.** The proof rule a gadget needs
is "a uniform mask pushed through a bijection is uniform", and on `PMF`
that is one lemma on *finite* types, `uniform_map_equiv (e : α ≃ β) :
(uniform α).map e = uniform β`, with the bijection supplied by Mathlib's
`Equiv` library (`subLeft`, `mulLeft₀`, `prodCongr`). The run of a
concrete circuit is unfolded by `simp` with the interpreter's equations
to "draw `v` uniform on `Fⁿ`, output `f v`, reveal `g v`", at which point
the lemma applies directly. A bijection on tapes would only have been a
way to *state* the same fact on a carrier where uniformity is an
assumption; on `PMF` uniformity of the joint draw is a theorem
(`seqUniform_eq_uniform`), so the tape had nothing left to do.

**Why joint uniformity must hold, and where it comes from.** A simulator
reproduces the whole list of revealed values, so the argument needs the
vector of masks to be uniform on `Fᵏ`, not each mask uniform on `F`.
Marginal uniformity is not enough (Beaver with `a = b` publishes
`x − y`), pairwise independence is not enough (`r₃ = r₁ + r₂` publishes
`x + y − z`); only joint uniformity makes the revealed vector the image
of a uniform vector under a bijection. In the tape model this is a
property of the measure on tapes that every bijection had to be checked
to preserve, which fails for infinite tapes and is counting for finite
ones. In the `PMF` model each coin is a fresh `bind` of `uniform F`, and
`n` fresh binds are one draw from `Fⁿ` by the monad laws plus one
computation (`uniform_prod`, `seqUniform_eq_uniform`); correlations draw
their `k` coins as a single `uniform (Fin k → F)` outright. This is the
substantive reason the tape went: the property the proofs rest on is a
consequence of the semantics rather than an assumption about it.

**Why evaluation survives without Layer 1.** Deterministic features are
modelled at `Id` and lifted (`Model.lift`), and `dist_lift` says the
`PMF` semantics of a coin-free circuit is the point at its evaluation; so
`rfl`/`decide` at `Id` are theorems at `PMF`, with no adequacy lemma to
prove. Circuits that draw coins are evaluated by `simp`, which is what a
tape would have needed too once the coin values are symbolic.

**What the compositional notion conditions on.** `Realizes` conditions
on the callee's declared *record* (public request kind and declared
leak), never on its output, and reproduces (response, view) jointly; the
adversary's view is the tagged trace (decision 012). The top-level
`Hiding` conditions on the output, as a convenience for circuits whose
output is public.

**What is proved.** `run_bind` (any lawful monad), `dist_bind`,
`dist_call`, `dist_lift`, `uniform_map_equiv`, `uniform_prod`,
`seqUniform_eq_uniform`, `handle_realizes`, `Realizes.comp`,
`Realizes.id`, `Hiding.transport`, `output_transport`, `cost_handle`,
`beaver_hiding`, `preHandler_realizes`, `invertGadget`,
`hiding_of_silent`, `leakyMul_not_hiding`. No `sorry` remains in the
sketch. VCVio was examined and not used: its oracle-computation monad
would replace `Circ` and `Model`, which already do the job with less.
