# Hybrids

A hybrid lists the ideal functionalities available to a program.
For example, `Std F` offers linear arithmetic, multiplication, and opening;
`Pre F` replaces multiplication with Beaver triples.
A program states which entries it needs using `Has` constraints.

## A List of Functionalities

The definition in [Weft/Functionality.lean](../Weft/Functionality.lean) is:

```lean
abbrev Hybrid := List Functionality
```

`fs.get i` selects the functionality at position `i : Fin fs.length`.
The interface of the whole hybrid dispatches by that position:

```lean
def Hybrid.ops (fs : Hybrid) : Interface where
  Op := (i : Fin fs.length) × (fs.get i).ops.Op
  dom o := (fs.get o.1).ops.dom o.2
  cod o := (fs.get o.1).ops.cod o.2
  leak o := (fs.get o.1).ops.leak o.2
```

An operation contains both the component index and the operation within that component.
The index also appears in events.
`fs.model` dispatches to the selected functionality's ideal model;
`fs.eval` dispatches to its evaluation model.
Hence the list fixes the meaning of every request.

Two functionalities can have the same interface and different models.
They remain different entries: being able to request a tuple of three shares does not establish that it is a Beaver triple.
Membership names the functionality, including its specification.

## Membership

`Has` witnesses a position and an equality:

```lean
class Has (F : Functionality) (fs : Hybrid) where
  i : Fin fs.length
  eq : fs.get i = F
```

`Has.here` selects the head of a list;
`Has.there` lifts a membership through another entry.
Instance search follows these constructors for literal lists.
The equality transports operand and response types when issuing a request with `Prog.op`.

For example, this membership is found without a user-written instance:

```lean
import Weft
open Weft

example : Has (Mult (ZMod 17)) (Std (ZMod 17)) := inferInstance
```

A function requiring `[Has (Mult F) fs]` accepts any hybrid providing that functionality.
It need not enumerate the other entries.
This is what lets us add a functionality without rewriting every program.

The representation permits duplicate entries.
A `Has` value selects one occurrence;
raw operation indices and event tags depend on list order.
The library does not identify different occurrences or declare their costs interchangeable.
Use explicit membership evidence or `Prog.opAt` when the position matters.

## Inclusion

Inclusion provides membership for every component of a hybrid:

```lean
class Incl (fs gs : Hybrid) where
  has : (i : Fin fs.length) → Has (fs.get i) gs
```

`Incl.refl` preserves each position.
`Incl.nil` and `Incl.cons` build inclusions into other lists.
`Prog.weaken` uses the supplied inclusion to embed a program over `fs` into `gs`;
`Prog.lift` handles the common case of prepending one functionality.

These operations reindex requests.
They do not implement an unavailable operation.
Replacing multiplication with Beaver preprocessing requires a [realisation](04-privacy.md), since `Pre F` does not contain `Mult F`.
The corresponding certified inclusion is `Realizations.incl`;
it reindexes the simulator's events as well.

## Standard Hybrids

[Weft/Std/Hybrids.lean](../Weft/Std/Hybrids.lean) defines:

| Hybrid | Entries, in order |
|---|---|
| `Std F` | `Lin F`, `Mult F`, `Reveal F` |
| `Pre F` | `Lin F`, `Reveal F`, `MulTriple F` |

`Bool2`, from [Weft/Std/Boolean.lean](../Weft/Std/Boolean.lean), contains `Lin GF2` and `Mult GF2`.
It does not include opening.

Helpers such as `Std.mult`, `Std.reveal`, and `Pre.triple` name the component operations when stating concrete views.
Each hybrid is an ordinary list;
there is no central enumeration to extend when adding a new functionality.

## Instantiation

A hybrid fixes semantics.
An `MPC` pairs each entry with a timed model to specify its cost.
`M.hybrid` forgets those models;
`M.model` and `M.eval` are the models of that underlying hybrid.

The same program and privacy proof can therefore be used with different cost instantiations.
`Std.mpc` and `Pre.mpc` provide convenient defaults;
their construction and the meaning of a timed model are covered in [Rounds](05-rounds.md).

[Previous: Functionalities](01-functionalities.md) · [Next: Programs](03-programs.md)
