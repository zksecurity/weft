# Privacy

To prove a program private, we specify a functionality and prove that the program realises it.
The specification fixes the output law and what may be disclosed.
The proof must reproduce the program's view from the specification's declared leakage, jointly with its output.

## Events

The view contains one event per request.
The definition in [Weft/Interface.lean](../Weft/Interface.lean) is:

```lean
structure Event (ι : Interface) where
  op : ι.Op
  leak : ι.leak op
```

The interpreter constructs an event from the request `r` and the sampled response/disclosure pair `(y, d)` as follows:

```lean
⟨r.op, d⟩
```

Only the operation identifier and the model's explicit disclosure are recorded.
The interpreter does not inspect operand or response shapes to determine observations.
Public operands, responses, or container lengths must be included in the model's
declared leakage when the functionality intends to disclose them.
Calls remain observable even when their leakage is `Unit`.

## The Realisation Equation

Let `F` be the specification and `fs` the implementation's hybrid.
[Weft/Realization.lean](../Weft/Realization.lean) defines:

```lean
structure Realization (F : Functionality) (fs : Hybrid) where
  impl : (D : Domain) → F.sig.Args D → Prog fs.ops D (F.sig.Resp D)
  Pre : F.sig.Args .ideal → Prop := fun _ => True
  Sim : F.sig.leak → PMF (List (Event fs.ops))
  real : ∀ r, Pre r → dist fs.model (impl .ideal r) = (do
    let (y, d) ← F.model.step r
    let s ← Sim d
    pure (y, s))
```

The left side is the real joint law of output and view.
On the right, we sample the ideal response and disclosure and give the disclosure to the simulator.
The full response `y` stays in the joint distribution;
the simulator receives only the declared disclosure.
The functionality has one fixed operation, so its simulator needs no selector.

The equality holds for every request satisfying `Pre`.
Hence correctness is exact: projecting the first component gives the ideal output law.
For a deterministic specification, the output is its specified value with probability one.

Why retain the joint law?
Consider a secret bit $x$, a uniform bit $b$, and a program that opens $x+b$ and returns the share $b$.
The opening alone is uniform.
A caller that opens the returned share can recover $x$.
A simulator must reproduce this correlation with the output;
matching the opening's marginal does not establish privacy.

## Constructing a Certificate

We proceed in four steps:

1. Define the functionality independently of the implementation.
2. Write an implementation generic in `D`, using only its hybrid's operations and clear computation. State any required `Pre`.
3. Construct `Sim` from the declared leakage. It must generate all concrete operation tags and declared disclosures.
4. Prove `real` by identifying the joint distributions, and declare the certificate with `program` to check its implementation.

For a small example, we specify multiplication with a public output.
The implementation calls multiplication and then reveal.
The declared leakage contains the product, so the simulator can reconstruct both events.
Unfolding the two deterministic calls gives the required equality:

```lean
import Weft
open Weft

namespace ProductExample
variable (F : Type) [Field F]

abbrev OpenProduct : Functionality :=
  .ofEval ⟨[.share F, .share F], .clear F, F⟩
    ⟨fun (x, y, ()) => let p := x * y; pure (p, p)⟩

def openProduct {fs : Hybrid} {D : Domain}
    [Has (Mult F) fs] [Has (Reveal F) fs]
    (a b : D.share F) : Prog fs.ops D (D.clear F) := do
  let p ← mul a b
  reveal p

program openProductReal : Realization (OpenProduct F) (Std F) where
  impl D r := openProduct F r.1 r.2.1
  Sim e := pure
    [event[Mult F] (),
     event[Reveal F] e]
  real r _ := by
    obtain ⟨a, b, ⟨⟩⟩ := r
    simp only [openProduct, mul, reveal, weft, Functionality.ofEval_model]
    rfl

end ProductExample
```

`Pre` defaults to `True` here.
The simulator receives the public product in `e`.
The multiplication event has `Unit` leakage;
the reveal event explicitly discloses the product.

For randomised implementations, unfolding yields a distribution over coins.
In [Examples/Beaver.lean](../Examples/Beaver.lean), the algebra proves that every mask pair produces the product.
The map $(a,b) \mapsto (x-a,y-b)$ is a bijection, so the opened pair is uniform.
`uniform_map_equiv` then identifies its distribution with the simulator's fresh pair.
This proves `beaverMult : Realization (Mult F) (Pre F)`.
The probability lemmas are in [Weft/PMF.lean](../Weft/PMF.lean).

## Preconditions and Composition

The specification remains total even if a particular implementation needs a precondition.
For example, masking-based inversion realises a silent inverse for $x \ne 0$.
Its implementation can also realise a total functionality that discloses whether $x = 0$;
these are different contracts.
Both proofs are in [Examples/Inversion.lean](../Examples/Inversion.lean).

A caller must establish the implementation's precondition at every reachable request.
`Valid M P c` expresses this: at a `call r k`, we need `P r`, and `Valid M P (k z.1)` for every `z` in `(M.step r).support`.
At `pure` there is no obligation;
at an ideal `look`, validity is that of the selected continuation.
Only supported responses matter.
Thus a caller can establish that a value from `RandNZ` is nonzero without inspecting a share in its implementation.

`Valid.of_forall` handles universally satisfied preconditions;
`Valid.bind` combines validity proofs for sequential programs.

`Realizations fs gs` supplies a realisation over `gs` for every component of `fs`.
Its constructors are `nil` and `cons`;
`impl`, `Pre`, and `Sim` dispatch to the component selected by the request or event.
`simList` runs the per-event simulators and concatenates their output lists.

For `g : Realizations fs gs` and `hc : Valid fs.model g.Pre c`, `handle_realizes` gives:

```lean
dist gs.model (Prog.handle (g.impl .ideal) c) = (do
  let r ← dist fs.model c
  let s ← simList g.Sim r.2
  pure (r.1, s))
```

The proof follows the caller's requests.
At each call it uses the component's realisation equation;
fresh simulator coins commute with the continuation's draws.
`output_transport` projects this equation to equality of output distributions.

`f.comp g` packages the composition of `f : Realization F fs` with `g : Realizations fs gs`.
Its implementation is inlining, its simulator is `f.Sim` followed by `simList g.Sim`, and its precondition is:

```lean
f.Pre r ∧ Valid fs.model g.Pre (f.impl .ideal r)
```

`Realization.incl F gs` realises `F` by calling its occurrence in `gs`.
The simulator embeds the declared leakage as an event at that position.
This is the base case for a primitive supplied by the hybrid.
`Realizations.incl` builds the corresponding family from an inclusion.

[Examples/AesHybrid.lean](../Examples/AesHybrid.lean) demonstrates composition using a toy block function.

## What `program` Checks

[Weft/Program.lean](../Weft/Program.lean) elaborates `program` as a noncomputable declaration of a realisation, reduces it to `Realization.mk`, and checks the fully applied `impl` field.
The simulator and proof may remain noncomputable.

The check rejects certificate parameters whose types mention `Weft.Domain`.
It inspects non-proof references in the implementation, rejects `sorry` and unsafe constants, and rejects noncomputable constants and `Classical.choice` in its strict initial traversal.
It follows references through package definitions, additionally rejecting `implemented_by`, `extern`, and `partial` there.
Inside computable definitions, Lean has already checked the computational relevance of noncomputable expressions;
proof terms are skipped.
Standard-library implementation details are trusted by the checker.

The check supplements domain polymorphism.
A bare `Realization` value does not contain a proof that this syntactic check succeeded, and `Realization.comp` does not enforce that its arguments were declared with `program`.
Use checked implementations as the components of a composed certificate.
The acceptance and rejection examples are in [Examples/Checked.lean](../Examples/Checked.lean).

## Statistical Realisations

[Weft/Statistical.lean](../Weft/Statistical.lean) defines `RealizationStat F fs`.
It has `impl`, `Pre`, and `Sim` as above, plus `ε : ENNReal` and two proof fields:

| Field | Obligation under `Pre r` |
|---|---|
| `output` | The real output marginal equals `F.response r` exactly |
| `close` | Total variation between the real and simulated joint laws is at most `ε` |

`F.response` is the response marginal of `F.model`.
The error bounds privacy;
it does not permit an erroneous output distribution.
`Realization.toStat` turns a perfect certificate into a statistical one with zero error.
The `program` command checks `Realization` declarations;
it does not accept `RealizationStat` directly.

For probability mass functions, the library defines total variation by:

$$
\operatorname{statDist}(p,q) = \sum_x \max(p(x)-q(x),0)
$$

The Lean definition uses truncated subtraction in `ENNReal`.
`PMF.statDist_bind_le` bounds a bind by the initial distance plus the expected continuation distance;
`PMF.statDist_map_le` bounds the effect of applying the same function to both distributions.

`budget M ε c` is the expected sum of per-request errors along the ideal execution.
It is zero at `pure`, adds `ε r.op` and the expected continuation budget at `call`, and follows the selected continuation at `look`.
The composition theorem bounding a caller's error by this budget remains unproved.
[Examples/Beaver.lean](../Examples/Beaver.lean) contains Beaver multiplication's zero-error statistical certificate and its proof.
[Examples/Statistical.lean](../Examples/Statistical.lean) demonstrates the bind-distance bound and a two-request error budget.

[Previous: Programs](03-programs.md) · [Next: Rounds](05-rounds.md)
