# Rounds

The round count follows dependencies between values.
If two multiplications use independent inputs, they can occupy the same round even when written sequentially in `do` notation.
A later multiplication using both results must wait for them.

Weft computes this by interpreting both shares and clear values as values with availability times.
The program's control clock records dependencies introduced by reading a clear value.

## Timed Values and Scheduling

The definitions in [Weft/Timed.lean](../Weft/Timed.lean) are:

```lean
structure Timed (T : Type) where
  val : T
  time : Nat

structure Price where
  delay : Nat
  comm : Nat

structure Clock where
  clock : Nat := 0
  comm : Nat := 0

abbrev Sched : Type → Type := StateT Clock Id
```

`Domain.timed` uses `Timed` for both `share` and `clear`.
`Timed.now x`, also written `⟪x⟫`, makes `x` available at round zero.
Clear arithmetic propagates the latest input time through the applicative;
it does not advance the control clock.
`Shape.ready` finds the latest time in a structured value, and `Operands.ready` does the same for a request's operands.

For the generic priced model `Model.timed E p`, an operation with latency $d$ returns its response at:

$$
t_{\mathrm{out}} = \max(t_{\mathrm{operands}},t_{\mathrm{clock}}) + d
$$

Every shared and clear response component is stamped with that time.
The model also charges the operation's communication price.
Issuing the request leaves the control clock unchanged;
its result carries the data dependency.

`Prog.look c k` waits until `c` is available, then runs `k` with its contents.
The timed `Look` instance updates the control clock to:

$$
t'_{\mathrm{clock}} = \max(t_{\mathrm{clock}},c.\mathrm{time})
$$

Subsequent requests inherit that clock even if their operands do not depend on `c`.
This accounts for control flow chosen after an opening.
The clock is monotone in the supplied instance;
leaving a branch does not reset it.

## Instantiating a Hybrid

An MPC supplies one timed model per functionality.
[Weft/MPC.lean](../Weft/MPC.lean) defines:

```lean
abbrev MPC.Entry := (F : Functionality) × Model F.ops .timed Sched
abbrev MPC := List MPC.Entry
```

`M.hybrid` is the list of functionalities, and `M.timed` dispatches to their timed models.
`M.model` remains the ideal model of the hybrid;
choosing a cost model does not redefine its semantics.

| Construction | Timed model |
|---|---|
| `F.priced p` | `Model.timed F.eval` with the same price for every operation |
| `F.pricedBy p` | `Model.timed F.eval` with a price per operation |
| `MPC.entry F T` | The supplied custom model `T` |
| `MPC.derived M f` | Run the realisation `f` under `M.timed` |

For example, `Std.mpc F` gives linear operations price `⟨0, 0⟩`, multiplication `⟨1, 2⟩`, and reveal `⟨1, 1⟩`.
The pairs are rounds and communication units.
`Std.timed F` is the resulting timed model.
These are parameters of the instantiation;
a functionality has no intrinsic latency.

## Independent Operations

The following two programs use three multiplications each.
The tree has two layers of dependencies;
the chain has three:

```lean
import Weft
import Examples.Timing
open Weft Weft.Examples.Timing

example (F : Type) [Add F] [Mul F] [Sub F] (a b c d : F) :
    delayOn (Std.timed F)
      (mul4seq (fs := Std F) (D := .timed) ⟪a⟫ ⟪b⟫ ⟪c⟫ ⟪d⟫) = 2 := rfl

example (F : Type) [Add F] [Mul F] [Sub F] (a b c d : F) :
    delayOn (Std.timed F)
      (chain3 (fs := Std F) (D := .timed) ⟪a⟫ ⟪b⟫ ⟪c⟫ ⟪d⟫) = 3 := rfl
```

The definitions are in [Examples/Timing.lean](../Examples/Timing.lean).
`mul4seq` first computes `a * b`, then `c * d`, then their product.
The first two results both become available at round one;
the final result is available at round two.
We do not need a parallel constructor to express this schedule.

Two reveals also overlap when their operands are independent.
Reading the first result with `look` before issuing the second serialises them.
Using the first result as a clear scalar instead adds a data dependency only to the operation using that scalar.
The `revealBoth`, `revealBothLook`, and `revealUseReveal` examples demonstrate these cases.

## Which Round to Measure

`Sched.run M c` runs from a zero clock and communication counter, returning the output and final state.
Input availability times come from the values passed to `c`.

| Observable | Meaning |
|---|---|
| `delayOn M c` | Maximum of a `Timed T` output's time and the final control clock |
| `readyOn M s c` | Maximum of all output times described by shape `s` and the final control clock |
| `Sched.now M c` | Final control clock |
| `Sched.output M c` | Output, including its availability times |

Use `readyOn` for a structured result, e.g. a pair of clear values.
Use `Sched.now` for a plain result whose dependencies were accounted for through `look`.
The control clock alone does not measure the availability of an unread timed result.
Neither `delayOn` nor `readyOn` waits for an unused response unless it contributes to the returned value or the control clock.

These measurements describe the run of the supplied timed model.
The generic model uses `F.eval`, including its fixed coins for randomised operations.
With random public control flow, one such run does not establish an expected or worst-case round bound over the ideal distribution.

## Composition

An implementation of $ab+c$ can start multiplying as soon as $a$ and $b$ are available.
Only the final addition needs $c$.
A single atomic latency applied after *all* operands arrive loses that overlap.

The exact timed instantiation of a realisation runs its implementation in the target model.
[Weft/Cost.lean](../Weft/Cost.lean) provides `Realization.timed` for one functionality and `Realizations.timed` for a hybrid.
For `g : Realizations fs gs`, a target timed model `T`, and a caller `c`, the scheduling theorem states:

```lean
Sched.run (g.timed T) c = Sched.run T (Prog.handle (g.impl .timed) c)
```

This is `Realizations.sched_timed`.
Its corollaries `Realizations.delayOn_timed` and `Realizations.readyOn_timed` give equality of the corresponding completion rounds.
The equation follows from interpreting the inlined implementation;
it requires no privacy precondition or fixed per-operation price.
It preserves output and scheduling state, not the abstract and concrete event lists.

Custom models accepted by `MPC.entry` carry no proof that they bound the implementation's timing.
Atomic prices and hand-written input profiles need a separate argument when used as bounds on a derived model.
The library proves exact agreement for the derived model;
it does not provide a general domination theorem for arbitrary profiles.
The compound-operation examples in [Examples/Timing.lean](../Examples/Timing.lean) compare these choices.

[Previous: Privacy](04-privacy.md) · [Next: Communication](06-communication.md)
