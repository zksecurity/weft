# Weft — verifying MPC programs in Lean 4

A library for writing MPC programs against ideal functionalities and
proving, in Lean 4 on Mathlib, that they are correct, what they cost in
rounds and communication, and that they are private, all against one
definition: a program **realises** a functionality when its run in the
hybrid is the functionality's step followed by a simulator that sees only
the adversary's record of that step.

* `DESIGN.md` — the design as it stands.
* `report.md` — the review that led to this version; its "Final design"
  section is the authoritative record of the 2026-09-05 revision.
* `decisions/` — one record per design choice: alternatives considered
  and why one won.

## Building

```
lake exe cache get   # Mathlib's cache, once
lake build           # the library and the examples
```

Lean 4.29, Mathlib v4.29.0.  A clean build of the library and every
example takes about a minute after the cache is fetched; the examples are
kept fast on purpose (see "Evaluating programs" below).

## The library, module by module

| Module | What it defines |
|---|---|
| `Weft/Shape.lean` | `Domain ⟨sh⟩` (a share of a `T`, per domain: `ideal`, `erased`, `timed`); the closed `Shape` language of responses with `interp` and `blank`; `Operands`. |
| `Weft/Interface.lean` | `Interface ⟨Op, dom, cod, disc, pubArg, ctrl⟩`: public operations with clear arguments, share operands, a response shape and a typed disclosure; `Req`, `Resp`, `Event ⟨op, out, leak⟩`. |
| `Weft/Prog.lean` | `Prog ι D`, the free monad of programs, polymorphic in the domain; `handle` inlines a program for each request. |
| `Weft/Model.lean` | `Model ι D m`: one joint `step` per request in a monad; `run`, `dist`, `output`, `view`, `cost`; the laws `run_bind`, `dist_bind`, `dist_call`. |
| `Weft/Timed.lean` | The timed domain: values carry a ready time, `Sched` threads the reveal and control clocks, `delayOn` reads the delay of a program off its data dependencies. |
| `Weft/Functionality.lean` | `Functionality ⟨ops, eval, IsModel, isModel_unique, timed⟩` with its semantics `model : Model ops .ideal PMF`; `Hybrid := List Functionality`; the certificate `Has F fs`; `Prog.op`. |
| `Weft/PMF.lean` | The facts about `PMF` the proofs need: the mask lemma `uniform_map_equiv` and friends. |
| `Weft/Std/Arith.lean` | `Lin`, `Mult`, `Reveal`, `Cmp`, `Inversion`, `Barrier`, each with an evaluation model, a `PMF` model and a hand-written timed model; the smart constructors `const`, `add`, `sub`, `smul`, `mul`, `reveal`, `lt`, `nativeInv`, `barrier`. |
| `Weft/Std/Random.lean` | `Rand`, `RandNZ`, `PubCoin`, and the preprocessing correlations `MulTriple`, `SquarePair`, `DoubleSharing` as functions of fresh coins. |
| `Weft/Std/Hybrids.lean` | The black box `Std F := [Lin F, Mult F, Reveal F]`, the preprocessing box `Pre F := [Lin F, Reveal F, MulTriple F]`, and the `weft` simp set that unfolds a program's semantics to "draw the coins, then a point". |
| `Weft/Realization.lean` | `Realization F fs ⟨impl, Pre, Sim, real⟩`; `Valid`, the discharge of preconditions on the support of the caller's run; `handle_realizes` (composition), `output_transport`, `Realization.comp`, `Realization.incl` (the trusted base). |
| `Weft/Cost.lean` | `Price ⟨delay, comm⟩`; an `MPC` is the hybrid list with a price per operation; `cost_handle`, the communication composition theorem. |
| `Weft/Statistical.lean` | Statistical realisations: exact output marginal, total variation on the joint; `PMF.statDist_bind_le`, the kernel lemma; the expected-call `budget` of a caller. |
| `Weft/Program.lean` | The `program` command: declares a `Realization` and checks that its fully applied implementation is a computable, domain-generic program. |

### The one privacy notion

```lean
structure Realization (F : Functionality) (fs : Hybrid) where
  impl : (D : Domain) → (r : Req F.ops D) → Prog fs.ops D (Resp F.ops D r.op)
  Pre  : Req F.ops .ideal → Prop := fun _ => True
  Sim  : Event F.ops → PMF (List (Event fs.ops))
  real : ∀ r, Pre r → dist fs.model (impl .ideal r) = do
    let p ← F.model.step r
    let s ← Sim ⟨r.op, (F.ops.cod r.op).blank p.1, p.2⟩
    pure (p.1, s)
```

The adversary's record of a request is the operation (constructor and
clear arguments), the clear part of the response, and the disclosure the
functionality declares; the simulator gets nothing else.  Composition is
`handle_realizes`: a caller valid for the realisation's precondition on the
support of its ideal run transports, with the simulators composed.  There
is no other privacy definition in the library; "this program leaks nothing
beyond its output" is the realisation of the one-operation functionality
that returns that output.

### Evaluating programs

A program is polymorphic in its domain and its hybrid, so the same
definition is evaluated under the ideal model (`output`, `view`), under a
price list (`cost`) and in the timed domain (`delayOn`).  Small generic
programs close by `rfl`.  For larger ones the examples state a closed
instance over `Fin 7` or `ZMod 17` and use `decide +kernel`, which is an
order of magnitude faster than `rfl` at that size.  The generic timed
model `Model.timed` is exact and is the default for a functionality, but
evaluating it by `rfl` is slow; every standard functionality carries a
hand-written `timed` model, which is what keeps the timed examples fast.

## The examples (`Examples/`)

Every example program comes with its four theorems: correctness by
evaluation, rounds in the timed domain, communication on a price list, and
privacy as a realisation.

* `Basic.lean` — the programs of the design notes (`sumAll`, `inner`,
  `mul3`, `prodTree`, `openMul`, `divByOpened`, `maxOf`, `horner`, …) and
  the shape of the theorems about them.
* `Beaver.lean` — the flagship: Beaver multiplication over
  `[Lin, Reveal, MulTriple]`, its realisation of `Mult` by the mask lemma,
  and the wrong triple box for which the realisation fails.
* `Gallery.lean` — matrix–vector product, log-depth product, public
  exponent, conditional swap, sorting network, binary search on a public
  array, zero test, a distance, S-boxes: what different programs look like.
* `Privacy.lean` — the black box over the preprocessing box, a program as
  a one-operation functionality, the two non-examples the old definitions
  got wrong, and composition.
* `Inversion.lean` — inversion by masking: a precondition (`x ≠ 0`)
  discharged by a caller through `Valid`, or a total functionality that
  discloses the zero test.
* `RandomCombination.lean` — a disclosure that is not a function of the
  response: the public coin of a random linear combination.
* `Silent.lean` — over `add` and `mul` alone, privacy needs a public-trace
  hypothesis.
* `Timing.lean` — delay from dependencies; atomic and profiled models of
  a compound operation.
* `AesHybrid.lean` — the UC shape: CBC realised over an AES-hybrid once,
  AES realised over the black box, composed by `Realization.comp`.
* `MultiField.lean` — programs generic over the field, conversions
  between fields as functionalities, daBits, edaBits, Boolean-to-arithmetic
  with its privacy proof.
* `Statistical.lean` — the statistical layer on Beaver.
* `Checked.lean` — what the `program` command rejects.

## What is not yet proved

* The statistical **budget theorem** (`Weft/Statistical.lean`): that the
  total variation of a caller's run is bounded by its expected-call
  `budget`.  The kernel lemma `PMF.statDist_bind_le` and the budget are
  there; the theorem itself is not yet stated.
* The **delay bound** for timing profiles: delay under an atomic latency
  model bounds delay under the inlined program only under a clock-aware
  hypothesis still to be stated (`Weft/Timed.lean`, `Examples/Timing.lean`).

No compositional theorem about correctness, communication or privacy is
left with `sorry`.
