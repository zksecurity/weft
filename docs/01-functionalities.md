# Functionalities

A functionality specifies what an operation returns and what it discloses.
For multiplication, the response is a share of the product;
for opening, it is a clear value.
These are different contracts, even when both evaluate to the same underlying field element.

We separate the *interface*, which specifies the available requests, from the *model*, which gives them meaning.
A functionality fixes an interface and one ideal model.
Its definition contains no price or scheduling policy.

## Domains and Shapes

A domain chooses how shared and clear values are represented.
The definition in [Weft/Shape.lean](../Weft/Shape.lean) is:

```lean
structure Domain where
  share : Type → Type
  clear : Type → Type
  apply : Applicative clear
```

`D.share F` is a share of an `F`;
`D.clear F` is a clear `F`.
The applicative supports computation on clear values without exposing their representation to the program.
A domain can represent several fields at once;
the field is its Lean type, with the algebraic instances required by each operation.

| Domain | Shared values | Clear values |
|---|---|---|
| `.ideal` | The underlying `T` | The underlying `T` |
| `.erased` | `Unit` | The underlying `T` |
| `.timed` | A value and its availability round | A value and its availability round |

`D.erase` erases shares while retaining `D`'s clear representation.
In particular, `.erased` is `.ideal.erase`.
The timed domain is defined in [Weft/Timed.lean](../Weft/Timed.lean).

Shapes describe operands and responses:

```lean
inductive Shape where
  | unit
  | clear (T : Type)
  | share (T : Type)
  | prod (a b : Shape)
  | vec (n : Nat) (a : Shape)
  | list (a : Shape)
```

`s.interp D` interprets a shape in a domain: `.share F` becomes `D.share F`, products become pairs, and `.vec n s` becomes a function from `Fin n` to `s.interp D`.
`Operands D ss` is a nested tuple with one value per shape in `ss`, ending in `Unit`.

`Shape.blank` replaces shared components by `()` and preserves clear components and container structure.
`Operands.blank` does the same for an operand tuple.
A list of shares still reveals its length after blanking;
`Shape.Hidden` means that a shape has no clear components, not that its structure is secret.

## Interfaces and Requests

The central definitions from [Weft/Interface.lean](../Weft/Interface.lean) are:

```lean
structure Interface where
  Op : Type
  dom : Op → List Shape
  cod : Op → Shape
  leak : Op → Type := fun _ => Unit

abbrev Resp (ι : Interface) (D : Domain) (o : ι.Op) : Type :=
  (ι.cod o).interp D

structure Req (ι : Interface) (D : Domain) where
  op : ι.Op
  args : Operands D (ι.dom op)
```

`Op` identifies the operation;
`dom` and `cod` give its operand and response shapes.
`leak` specifies the type of additional disclosure.
It may depend on the operation.
`Unit` denotes no additional disclosure.

For example, `Mult.ops F` has one operation, two shared operands, and one shared response.
A request at the ideal domain is `⟨.mult, (x, y, ())⟩`.
`Reveal.ops F` instead has one shared operand and a clear response.
A public scalar passed to `Lin.smul` is a `.clear F` operand, so it is recorded in the request event.

The operation identifier is public too.
Secret data belongs in shared operand shapes;
putting it in `Op` makes it part of the view.

## Models

A model supplies a joint response and disclosure for each request.
Its definition is in [Weft/Model.lean](../Weft/Model.lean):

```lean
structure Model (ι : Interface) (D : Domain) (m : Type → Type) where
  step : (r : Req ι D) → m (Resp ι D r.op × ι.leak r.op)
```

The joint step matters when response and disclosure share randomness.
Sampling them independently would specify a different functionality.
`Model.program` projects the response marginal from `step`.

| Constructor | Meaning |
|---|---|
| `Model.det` | Deterministic response and disclosure, lifted into a monad |
| `Model.silent` | Deterministic response with `Unit` disclosure |
| `Model.lift` | An `Id` model lifted into another monad |

An ideal model uses `D := .ideal` and `m := PMF`.
It can inspect the underlying operands to implement the specification.
An evaluation model uses `Id`.
Models in other domains support other interpretations, e.g. the scheduling model used to count rounds.

`Model.silent` still produces request events.
Clear operands and clear responses are recorded by the interpreter independently of the model's disclosure field.
In particular, `Reveal` uses a silent model: its clear response already says what was opened.

## Fixing the Meaning

A functionality fixes a unique ideal model.
The definition from [Weft/Functionality.lean](../Weft/Functionality.lean) is:

```lean
structure Functionality where
  ops : Interface
  eval : Model ops .ideal Id
  IsModel : Model ops .ideal PMF → Prop
  isModel_unique : ∃! M, IsModel M
```

`F.model` selects the unique model satisfying `F.IsModel`.
For a known model `M`, the usual definition is `IsModel := (· = M)`;
`Functionality.unique_eq` supplies uniqueness and `Functionality.model_eq` identifies the selected model.

Why use a predicate?
`PMF` models are generally noncomputable.
Storing one directly would make the functionality value noncomputable, including programs whose types mention a literal hybrid containing it.
The predicate keeps the value computable while fixing its semantics exactly.

`eval` supports deterministic evaluation.
Randomised functionalities supply fixed dummy coins here;
an evaluation run is not a probabilistic correctness or privacy proof.
The structure does not require `eval` to agree with `model`.
For deterministic functionalities, `Functionality.ofEval ι E` fixes the ideal model to `E.lift PMF`, making that agreement explicit.

Here is a complete deterministic specification for returning a product in the clear:

```lean
import Weft
open Weft

abbrev OpenProduct (F : Type) [Mul F] : Functionality :=
  .ofEval
    ⟨Unit, fun _ => [.share F, .share F], fun _ => .clear F,
      fun _ => Unit⟩
    ⟨fun r => pure (r.args.1 * r.args.2.1, ())⟩
```

The specification is total.
Restrictions needed by a particular implementation belong to its [realisation](04-privacy.md).

## Standard Functionalities

The arithmetic operations are in [Weft/Std/Arith.lean](../Weft/Std/Arith.lean);
randomness is in [Weft/Std/Random.lean](../Weft/Std/Random.lean).

| Functionality | Response or operations |
|---|---|
| `Lin F` | Constants, addition, subtraction, and multiplication by a clear scalar |
| `Mult F` | A shared product |
| `Reveal F` | A share's value in the clear |
| `Cmp F` | A shared indicator for the supplied order on `F` |
| `Inversion F` | A shared inverse; fields use Mathlib's convention $0^{-1} = 0$ |
| `Rand F` | A uniform shared element |
| `RandNZ F` | A uniform shared nonzero element |
| `PubCoin F` | A uniform clear element |
| `MulTriple F` | Shares of $(a,b,ab)$ for independent uniform $a,b$ |
| `SquarePair F` | Shares of $(r,r^2)$ for uniform $r$ |
| `DoubleSharing F` | Two shares of the same uniform element |

The assumptions are per functionality.
Linear arithmetic needs the corresponding operations on `F`;
it does not require every `F` to be a field.
Sampling requires a finite nonempty space.
Comparison uses an explicit `LT` instance;
there is no canonical field order.

Correlated randomness is specified by `Correlation R T`, with `k : Nat` and `build : (Fin k → R) → T`.
Its `sample` draws uniformly from `Rᵏ` and applies `build`.
For a Beaver triple, `k = 2` and `build a = (a 0, a 1, a 0 * a 1)`.

[Weft/Std/Boolean.lean](../Weft/Std/Boolean.lean) supplies Boolean arithmetic over `GF2 := ZMod 2`.
[Examples/MultiField.lean](../Examples/MultiField.lean) defines cross-type conversion and correlation examples.
Conversion is an operation with its own specification;
the domain does not silently coerce shares between fields.

[Previous: Universal Composability](00-universal-composability.md) · [Next: Hybrids](02-hybrids.md)
