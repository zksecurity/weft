# Communication

Communication is additive across requests.
Two operations can overlap in rounds and still incur both communication costs.
The unit is chosen by the cost model, e.g. field elements or bytes;
Weft does not impose an encoding or derive prices from a network protocol.

There are two ways to account for it: a counter in a timed run, and an additive trace cost under the ideal semantics.
The former supports the derived timed instantiations from [Rounds](05-rounds.md).
The latter gives a distribution over costs when ideal randomness affects the caller's requests.

## The Scheduling Counter

`Clock.comm` accumulates the communication charged during a scheduled run.
`Clock.pay c` adds `c` to that counter and leaves the control clock unchanged.
The generic `Model.timed E p` charges `(p r.op).comm` at each request.
`commOn M c` extracts the final counter from `Sched.run M c`.
The definitions are in [Weft/Timed.lean](../Weft/Timed.lean).

Recall that `Std.timed F` prices multiplication at two communication units.
The multiplication tree and chain from the rounds example therefore have the same communication cost:

```lean
import Weft
import Examples.Timing
open Weft Weft.Examples.Timing

example (F : Type) [Add F] [Mul F] [Sub F] (a b c d : F) :
    commOn (Std.timed F)
      (mul4seq (fs := Std F) (D := .timed) ⟪a⟫ ⟪b⟫ ⟪c⟫ ⟪d⟫) = 6 := rfl

example (F : Type) [Add F] [Mul F] [Sub F] (a b c d : F) :
    commOn (Std.timed F)
      (chain3 (fs := Std F) (D := .timed) ⟪a⟫ ⟪b⟫ ⟪c⟫ ⟪d⟫) = 6 := rfl
```

Every issued operation is charged, including one whose response is unused.
Neither `pure` nor the supplied timed `look` instance adds communication.

`Pre.mpc F` gives Beaver triples price `⟨0, 0⟩` by default.
This is an accounting choice: preprocessing has been supplied without a charge in that model.
To include its cost, supply a triple price or derive the entry from a realisation producing triples.
The functionality itself does not change.

## Communication under Derived Instantiations

For `g : Realizations fs gs`, `g.timed T` runs each component's implementation under the target timed model `T`.
The theorem `Realizations.commOn_timed` in [Weft/Cost.lean](../Weft/Cost.lean) gives:

```lean
commOn (g.timed T) c = commOn T (Prog.handle (g.impl .timed) c)
```

This is a projection of the scheduling equality from the previous chapter.
There is no fixed-price hypothesis: the derived model runs the implementation, including whatever requests that execution makes.
Both sides use the same timed computation.
As with round measurements, fixed evaluation coins do not turn this into a claim about expected communication under random public control flow.

## Additive Cost Models

For a distributional statement, we price the operations observed by the ideal interpreter.
[Weft/Model.lean](../Weft/Model.lean) defines:

```lean
structure CostModel (ι : Interface) (C : Type) where
  op : ι.Op → C
```

`run` requires `[AddMonoid C]` and adds these prices into `Trace.cost`.
The price depends on the operation identifier;
it does not receive the request's operand tuple.
`C := Nat` counts one resource, while a product of additive types can count several.
`CostModel.unit` disables this trace accounting.

`cost M K c` gives the cost of one `Id` evaluation.
`costDist M K c`, from [Weft/Cost.lean](../Weft/Cost.lean), projects the cost from a `PMF` run:

```lean
noncomputable def costDist {ι : Interface} {D : Domain} {C α : Type}
    [AddMonoid C] [Look D PMF] (M : Model ι D PMF)
    (K : CostModel ι C) (c : Prog ι D α) : PMF C :=
  (fun r => r.2.cost) <$> run M K c
```

The model determines the joint distribution of responses and disclosures.
The continuation can use clear responses to decide which requests to make next;
hence its cost can be random even though each operation has a fixed price.
Changing `K` does not change the output law, as proved by `run_fst`.

The scheduling counter and `Trace.cost` are separate mechanisms.
Scheduled observations such as `commOn` use `CostModel.unit` for the trace and read the counter instead.
There is no automatic conversion from an arbitrary timed model to an ideal `CostModel`.

## Transporting a Price through a Realisation

Suppose `g : Realizations fs gs` implements an abstract hybrid `fs` over `gs`.
We want an abstract price model `p` to match concrete prices `K`.
The predicate `Priced gs.model (g.impl .ideal) K p` requires every implementation request to have exactly its abstract operation's cost:

```lean
∀ r, costDist gs.model K (g.impl .ideal r) = pure (p.op r.op)
```

This obligation quantifies over every request, independently of the realisation's `Pre`.
The cost must be fixed across operands and random coins for each operation identifier.
An average-cost equality is insufficient.

With this `Priced` proof and `hc : Valid fs.model g.Pre c`, `cost_handle` gives:

```lean
costDist gs.model K (Prog.handle (g.impl .ideal) c) =
  costDist fs.model p c
```

The caller's cost may still be random: different ideal executions can issue different sequences of operations.
The theorem preserves that whole distribution.
Its proof uses the realisation's exact output marginal to match the caller's continuations, and `Priced` to replace each implementation cost with the corresponding abstract price.

Costs that depend on operands or random coins do not satisfy this fixed-price contract in general.
They can be studied directly with `costDist`, or measured for a scheduled execution through a custom or derived timed model.
Neither route supplies a bound automatically.

[Previous: Rounds](05-rounds.md)
