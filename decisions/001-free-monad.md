# 001 — Circuits as a free monad with Lean continuations

## Choice
A circuit is a program in the free monad over the functionality's
signature (`Circ σ α` with `pure` and `call`, plus a `par` node kept as an
option, see 002). Continuations are ordinary Lean functions. Circuits are
written in `do`-notation.

## Alternatives
1. **First-order DAG / netlist.** Wires as indices, gates as nodes; the
   circuit is inspectable data. Pro: dependency analysis, scheduling and
   symbolic privacy checks are syntactic; the round count is a graph
   property. Con: "reveal, compute in the clear, insert back" and any
   branching on revealed values need an ad-hoc control-flow layer; clear
   computation has to be re-encoded as nodes; loses `do`-notation.
2. **Tagless-final (typeclass of operations, no syntax).** Pro: maximal
   polymorphism, cheap. Con: no syntax to interpret twice (semantics and
   cost need two instances of the class, and nothing relates them); no
   handlers, hence no realisations.
3. **Free applicative + monad (Haxl-style batching).** Pro: automatic
   parallelism of independent calls. Con: the round count depends on a
   normalisation the programmer does not see; `do` desugars to `bind`, so
   independence is invisible without an `ApplicativeDo`-style macro.

## Why the free monad
The reactive pattern is the common case in MPC circuits, and it is
exactly a monadic bind with a clear-valued continuation. Handlers
(`Circ.handle`) are the mechanism for realising one functionality by
circuits over another, which is what makes composition work (006). What
is lost, syntactic inspectability, is recovered where needed by running
the same circuit in other domains (007): the timed domain for delay, a
symbolic domain for automatic privacy checks.

## Consequence to keep in mind
Because continuations are opaque, the composition theorems are proved by
induction over the run (a hybrid argument along the trace), not by
transformation of the syntax.
