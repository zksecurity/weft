# Programs

A program issues requests to a hybrid and computes on the responses.
We write it in Lean's `do` notation.
Shared values can be passed to operations;
clear values support ordinary computation and control flow.

The program is generic in its domain.
The same definition can therefore be interpreted over ideal values for semantics and timed values for rounds and communication.

## Requests and Continuations

[Weft/Prog.lean](../Weft/Prog.lean) defines the program language:

```lean
inductive Prog (ι : Interface) (D : Domain) : Type → Type 1 where
  | pure {α : Type} : α → Prog ι D α
  | call {α : Type} (r : Req ι D) :
      (Resp ι D r.op → Prog ι D α) → Prog ι D α
  | look {α T : Type} (c : D.clear T) :
      (T → Prog ι D α) → Prog ι D α
```

`pure` returns a value.
`call` issues a request and gives its response to the continuation.
`look` reads a clear value so the continuation can depend on its contents.
The `Monad` instance substitutes continuations;
its laws are proved in the same module.

Continuations are Lean functions.
This makes the usual MPC pattern convenient: open a share, compute in the clear, and use the result in another request.
It also means that a program is not an inspectable netlist.
The library interprets the program to obtain its semantics and costs;
it does not recover a circuit graph from arbitrary Lean functions.

`Prog.req` issues a raw interface request.
`Prog.op` uses `Has` to issue a request to a component of a hybrid.
Most code uses the typed helpers `mul`, `reveal`, `rand`, etc., which construct those requests.

## Writing a Program

Consider two dependent multiplications.
Their definition and output evaluation are:

```lean
import Weft
open Weft

def multiply3 {F : Type} [Mul F] {fs : Hybrid} {D : Domain}
    [Has (Mult F) fs] (a b c : D.share F) :
    Prog fs.ops D (D.share F) := do
  let ab ← mul a b
  mul ab c

example (F : Type) [Mul F] (a b c : F) :
    output (Hybrid.eval [Mult F])
      (multiply3 (fs := [Mult F]) (D := .ideal) a b c) = a * b * c := rfl
```

The program needs multiplication and nothing else.
In the ideal domain, shares reduce to their values, so the deterministic run reduces to the claimed expression.
For a randomised functionality, an evaluation with fixed coins proves only what that evaluation does;
use `dist` for a statement about its ideal distribution.

## Clear Values and Control Flow

`D.clear` has an applicative instance.
Arithmetic lifts through it: if `u v : D.clear F`, then `u * v : D.clear F`.
A plain constant can be embedded with `pure` or the provided coercion.
In the timed domain, the result inherits the latest input time.

Branching requires the contents of a clear value.
We obtain them with `Prog.look`:

```lean
import Weft
open Weft

def multiplyUnlessZero {F : Type} [Mul F] [Zero F] [DecidableEq F]
    {fs : Hybrid} {D : Domain} [Has (Mult F) fs] [Has (Reveal F) fs]
    (x y : D.share F) : Prog fs.ops D (D.share F) := do
  let opened ← reveal x
  Prog.look opened fun a =>
    if a = 0 then pure y else mul x y
```

The opening discloses `x`.
`look` itself adds no event;
it lets later requests depend on that disclosure.
In the ideal domain it applies the continuation immediately.
In the timed domain it waits for the clear value before allowing subsequent requests.
The resulting control dependency is explained in [Rounds](05-rounds.md).

A program may branch on an ordinary public parameter without `look`.
Such a parameter is already available.
Values obtained from operations remain inside `D.clear` until read;
that distinction is what lets the timing interpretation account for their availability.

## Interpretation

[Weft/Model.lean](../Weft/Model.lean) defines `run`.
Given a model `M` and an additive cost model `K`, it returns the output and a trace:

```lean
structure Trace (ι : Interface) (D : Domain) (C : Type) where
  cost : C
  view : List (Event ι D)
```

At each `call`, `run` samples `M.step r`, records one event, and runs the continuation on the response.
Sequential composition adds costs and concatenates event lists.
At each `look`, it invokes the domain's `Look` instance and continues without recording another event.

| Observable | Interpretation | Result |
|---|---|---|
| `output M c` | `Id` | Output of one evaluation |
| `view M c` | `Id` | Its event list |
| `cost M K c` | `Id` | Its additive cost |
| `dist M c` | `PMF` | Joint distribution of output and event list |

`run_bind` and `dist_bind` decompose sequential execution into the first run and a continuation run.
`run_fst` proves that changing the additive cost model does not change the output distribution.
The timed observables use `Sched` and are covered in the two cost chapters.

For semantic proofs, `simp [weft, myProgram]` unfolds interpreter laws, hybrid dispatch, and standard functionality models.
Small deterministic examples often close with `rfl`.
Larger closed evaluations in the examples use `decide +kernel`;
probabilistic proofs work with the resulting `PMF` expressions.

## Handling and Checked Implementations

`Prog.handle h c` replaces every request in `c` with the program returned by `h`.
The handler must return the requested response type.
It preserves `pure` and `look`, and recursively handles the continuation after each substituted call.
This is the operation used for realisation composition.
`Prog.weaken` is the special case that reissues requests through a hybrid inclusion.

Domain polymorphism makes a share abstract to the implementation.
The `program` command adds checks on the fully applied implementation term, including restrictions on domain-dependent parameters and noncomputable code.
A declaration of type `Realization` alone does not record that this check ran.
The command and its precise scope are covered in [Privacy](04-privacy.md).

More examples are in [Examples/Basic.lean](../Examples/Basic.lean) and [Examples/Gallery.lean](../Examples/Gallery.lean).

[Previous: Hybrids](02-hybrids.md) · [Next: Privacy](04-privacy.md)
