# Functionalities

A functionality specifies what an operation returns and what it discloses.
For multiplication, the response is a share of the product;
for opening, it is a clear value.
These are different contracts, even when both evaluate to the same underlying field element.

A *signature* specifies the input, response, and leakage types of one function;
a *model* gives that function meaning.
A functionality fixes one signature and one ideal model.
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
These are representation utilities; the interpreter does not use them to construct events.

## Signatures and Requests

Each functionality has one operation with a fixed signature.
The definitions from [Weft/Interface.lean](../Weft/Interface.lean) are:

```lean
structure Signature where
  dom : List Shape
  cod : Shape
  leak : Type := Unit

abbrev Signature.Args (σ : Signature) (D : Domain) : Type :=
  Operands D σ.dom

abbrev Signature.Resp (σ : Signature) (D : Domain) : Type :=
  σ.cod.interp D
```

`dom` and `cod` give the operand and response shapes.
`leak` specifies the type of explicit disclosure; `Unit` denotes no value disclosure.
For example, `Mult.sig F` has two shared operands and one shared response.
Its ideal operands are `(x, y, ())`, with no operation selector.
`Reveal.sig F` has one shared operand, a clear response, and leakage type `F`.
Its model returns `(x, x)`, explicitly disclosing the opened value.
`Const F` and `Smul F` explicitly disclose their public constant or scalar.
The interpreter does not derive disclosure from `.clear` shapes.

A [hybrid](02-hybrids.md) offers several functionalities.
Its interface selects a functionality by position and obtains the types from its signature:

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

The selected position is public and appears in the view.
Secret data belongs in shared operand shapes; putting it in `Op` makes it public.
There is no selector within an individual functionality.

## Models

A function model supplies a joint response and disclosure for each operand tuple.
Its definition is in [Weft/Model.lean](../Weft/Model.lean):

```lean
structure FunctionModel (σ : Signature) (D : Domain) (m : Type → Type) where
  step : σ.Args D → m (σ.Resp D × σ.leak)
```

A deterministic evaluation model specifies both the response and disclosure explicitly.
For addition, the response is the sum and the disclosure is `()`:

```lean
def addEval (F : Type) [Add F] : FunctionModel (Addition.sig F) .ideal Id :=
  ⟨fun (a, b, ()) => pure (a + b, ())⟩
```

The joint step matters when response and disclosure share randomness.
Sampling them independently would specify a different functionality.
`FunctionModel.response` projects the response marginal from `step`;
`FunctionModel.leakage` projects the disclosure marginal.
These accessors do not override either value or let a simulator program randomness.
Use `step` when both components are needed together: independently sampling the marginals does not preserve their correlation.

| Constructor | Meaning |
|---|---|
| `FunctionModel.det` | Deterministic response and disclosure, lifted into a monad |
| `FunctionModel.lift` | An `Id` model lifted into another monad |

An ideal model uses `D := .ideal` and `m := PMF`.
It can inspect the underlying operands to implement the specification.
An evaluation model uses `Id`.
Models in other domains support other interpretations, e.g. the scheduling model used to count rounds.

Calling a functionality with `Unit` disclosure still produces an event containing its hybrid position and `()`.
Operand and response shapes do not add observations.
Each functionality declares its intended disclosure explicitly:
`Reveal` returns and discloses its operand, and `PubCoin` returns and discloses its sampled coin.
Their `.leakage` marginals therefore describe those values.

The hybrid interpreter uses `Model ι D m`, whose `step` takes a `Req ι D`.
For a hybrid, it dispatches to the selected functionality's `FunctionModel.step` with the request's operands.

## Fixing the Meaning

A functionality fixes a unique ideal model.
The definition from [Weft/Functionality.lean](../Weft/Functionality.lean) is:

```lean
structure Functionality where
  sig : Signature
  eval : FunctionModel sig .ideal Id
  IsModel : FunctionModel sig .ideal PMF → Prop
  isModel_unique : ∃! M, IsModel M
```

`F.model` selects the unique model satisfying `F.IsModel`.
For a known model `M`, the usual definition is `IsModel := (· = M)`;
`Functionality.unique_eq` supplies uniqueness and `Functionality.model_eq` identifies the selected model.
`F.response r` and `F.leakage r` expose the two marginals of that model;
`F.model.step r` retains their joint distribution.

Why use a predicate?
`PMF` models are generally noncomputable.
Storing one directly would make the functionality value noncomputable, including programs whose types mention a literal hybrid containing it.
The predicate keeps the value computable while fixing its semantics exactly.

`eval` supports deterministic evaluation.
Randomised functionalities supply fixed dummy coins here;
an evaluation run is not a probabilistic correctness or privacy proof.
The structure does not require `eval` to agree with `model`.
For deterministic functionalities, `Functionality.ofEval σ E` fixes the ideal model to `E.lift PMF`, making that agreement explicit.

Here is a complete deterministic specification for returning a product in the clear:

```lean
import Weft
open Weft

abbrev OpenProduct (F : Type) [Mul F] : Functionality :=
  .ofEval ⟨[.share F, .share F], .clear F, F⟩
    ⟨fun (x, y, ()) => let p := x * y; pure (p, p)⟩
```

The specification is total.
Restrictions needed by a particular implementation belong to its [realisation](04-privacy.md).

## Standard Functionalities

The arithmetic operations are in [Weft/Std/Arith.lean](../Weft/Std/Arith.lean);
randomness is in [Weft/Std/Random.lean](../Weft/Std/Random.lean).

| Functionality | Response |
|---|---|
| `Const F` | A share of a public constant; discloses that constant |
| `Addition F` | A shared sum |
| `Subtraction F` | A shared difference |
| `Smul F` | A share scaled by a clear scalar; discloses that scalar |
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
