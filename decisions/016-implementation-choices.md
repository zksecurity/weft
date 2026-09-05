# 016 — Implementation choices of the 2026-09 rewrite

Choices made while implementing the final design of `report.md` that the
design left open or did not anticipate.  Each is small; together they
determine what the library looks like.

## Semantics is a predicate, so that programs stay computable
A `Functionality` does not store its `PMF` model.  It stores an
evaluation model `eval : Model ops .ideal Id`, a predicate
`IsModel : Model ops .ideal PMF → Prop` and a proof that exactly one
model satisfies it; `Functionality.model` is that model, by choice.
Reason: `PMF` values are noncomputable, and a program over a literal
hybrid `[Lin F, Reveal F, MulTriple F]` mentions the functionality
values in its type; with the model as a field every such program would
be noncomputable and the `program` command could certify nothing.  The
standard functionalities are `abbrev`s, so that `Has` instances are found
by unfolding, and each has a `model_eq` simp lemma.

## An evaluation model per functionality
`eval` gives every functionality a deterministic run (`output`, `view` by
`rfl` or `decide`), with a fixed dummy for randomised operations (values
under it are meaningless by design).  A first version also gave each
functionality a timed model; that was wrong, and is reversed by decision
017: cost is an instantiation of the hybrid, and the hand-written timed
models live beside the functionalities, in the MPC.

## Disclosure is typed per operation
`Interface.leak : Op → Type` replaces the report's `List Pub`
(decision 014).  `Event ⟨op, args, out, leak⟩` is then a dependent record;
`Event.shift` reindexes it along a hybrid.

## No scheduling metadata on the interface
A first version had two trusted flags, `pubArg` (the operation carries a
clear argument, so it waits for the reveal clock) and `ctrl` (the
operation is a barrier).  Both are gone: a clear operand is a clear shape
in `dom`, so the timed model reads `Operands.hasClear`; and `Barrier` is
the one functionality with a timed model of its own, which raises the
control clock.

## Evaluation performance
Evaluation by `rfl` was exponential in the number of requests, for three
reasons, all pattern matches the elaborator re-forced at every reference:
pairs in the interpreter and the operand helpers (projections now), the
scheduling state rewritten per request (`Clock.after` returns the state
itself when nothing changes) and a shape dispatch on every use of a
response (`Shape.withTimed` matches once).  `Sched` must stay
`StateT Clock Id`: its pattern-matching bind forces a step exactly once.
Policy for examples: `rfl` for small generic programs; a closed instance
over `Fin 7` or `ZMod 17` and `decide +kernel` for larger ones, an order
of magnitude faster.  A clean `lake build` of library and examples is
about a minute.

## The `program` command
Elaborates a `noncomputable def` of type `Realization F fs`, reduces the
body to `Realization.mk` and walks the implementation's constants: it
rejects `sorry` and `unsafe` everywhere, `noncomputable` and
`Classical.choice` in the certificate's own term; for the package's own
definitions it also rejects `implemented_by`, `extern` and `partial` and
recurses into them; the standard library's externs are its own business.  Parameters whose type mentions `Weft.Domain` are
rejected, so an implementation cannot be handed a domain-specific
operation.  What it does not check is that a composed certificate
(`Realization.comp`) was built from checked parts; `comp` inlines checked
programs, so the property is preserved, but not re-verified.

## Open
The duplicate-entry and reindexing policy for list hybrids and price
lists; the delay bound for timing profiles; the statistical budget
theorem.
