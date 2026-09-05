# 015 — One certificate: realisation of an explicit functionality

## Question
The old design had four privacy-shaped notions: `Hiding` (a program
leaks nothing beyond its output), `Gadget` (a program with assumptions,
spec, allowed leakage and two proofs), `RealizesStat` (a statistical
variant), and untagged leaf theorems (`beaver_hiding`, `hiding_of_silent`)
that were to be transported to tagged statements.  The report found that
`Gadget` certified a program against its own output distribution and
could not compose when it carried an assumption (Issue 4), that the
statistical variant permitted output error and had no composition lemma
(Issue 6), and that untagged proofs do not transport in general
(Issue 7).

## Choice
One notion.  A privacy statement is a `Realization F fs`: a program
`impl` for every domain, a simulator `Sim` from the event of `F` to a list
of events of `fs`, and the equation

    dist fs.model (impl .ideal r) =
      do let p ← F.model.step r
         let s ← Sim ⟨r.op, blank p.1, p.2⟩
         pure (p.1, s)

under a precondition `Pre r` on the request.  Everything else is a
consequence or a special case:

* **Specifications are functionalities**, written independently of the
  program (a `Functionality` is total, and its `model` is the whole
  meaning).  "This program leaks nothing beyond its output" is the
  realisation of the one-operation functionality returning that output.
* **Assumptions are preconditions** on the realisation, not on the
  functionality (which stays total).  A caller discharges them with
  `Valid`: every request it issues, on the support of its ideal run,
  satisfies `Pre`.  Inversion by masking realises the silent `Invert` for
  `x ≠ 0`, and a caller that inverts the output of `randNZ` is valid
  (`Examples/Inversion.lean`).  The same program realises, with no
  precondition, the total functionality that discloses whether `x = 0`;
  the two are different functionalities under their own names.
* **Composition** is one theorem, `handle_realizes`: inlining
  realisations of the components of `fs` into a caller that is valid for
  their preconditions gives a realisation over the target hybrid, with
  the simulators composed.  `Realization.comp` is its corollary on
  certificates; `Realization.incl`, that calling `F` realises `F` in any
  hybrid containing it, is the trusted base; correctness transports as a
  corollary (`output_transport`) and communication the same way
  (`cost_handle`).
* **Statistical** realisations keep the output marginal exact and bound
  total variation on the joint distribution of output and view, per
  operation; `PMF.statDist_bind_le` is the kernel lemma of their
  composition, and a caller's expected-call `budget` sums its errors.
* **Certificates are built by the `program` command**, which checks the
  fully applied implementation: computable, no `unsafe`, `implemented_by`,
  `partial` or `noncomputable` definition, and no parameter whose type
  mentions a domain.  A polymorphic `impl` can do nothing with a share
  except pass it to an operation, which is what makes "the simulator sees
  only the event" mean what it says.

## Alternatives
* **Keep gadgets and functionalities distinct** (report, Section 4).
  Rejected: a gadget's self-derived spec is not an independent
  specification, and a caller cannot state `x ≠ 0` about a share it holds
  polymorphically.  A gadget is a realisation whose functionality has one
  operation.
* **Statements at the ideal domain only.**  Rejected: `shapeLeak`
  branches on a share's value at the ideal domain and is hiding there;
  quantifying over the domain, and checking the applied term, closes this.
* **An efficiency certificate for simulators** and the interactive
  embedding that would give computational security from a perfect hybrid
  step.  Not planned; the transfer is stated as a conditional external
  application (`DESIGN.md` §2.11).

## Consequences
`Hiding`, `Gadget`, `RealizesStat` and the untagged leaf theorems are
gone; every old privacy claim is restated as a realisation
(`Examples/Beaver.lean`, `Privacy.lean`, `Inversion.lean`, `Silent.lean`,
`MultiField.lean`) and two of them are now proved *false* in the form the
old definitions accepted (`leakyMul_not_realizes`,
`openKeep_not_realizes`).  Functionalities are stateless `PMF` kernels;
stateful functionalities (sessions, batched checks, amortised
preprocessing) are out of scope.  The budget theorem is not yet stated.
