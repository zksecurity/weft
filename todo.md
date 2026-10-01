# TODO

- [x] Make explicit functionality leakage the source of adversarial value disclosure.

  Have `Reveal` declare `leak := F` and return `(x, x)` from its model:
  the clear response remains `x`, and the declared leakage is also `x`.

  Refactor event construction and privacy/simulation definitions so public values
  are disclosed through explicit leakage. When recording adversarial observations,
  the interpreter must not infer disclosure from `.clear`, `.share`, or other
  shapes, including through `Operands.blank` or `Shape.blank`. Each functionality
  specifies what it discloses; the interpreter records its declared leakage.

  Update the other functionalities to declare their intended disclosures, and
  adjust the documentation and privacy/composition proofs accordingly.

- [x] Restrict each functionality to a single function/operation.

  Split multi-operation functionalities such as `Lin` into separate
  functionalities. Remove per-functionality operation selectors and simplify
  input, output, and leakage types; hybrids select the functionality directly.
  Update models, program calls, realizations, and examples to match.

## Possible future considerations

- Eventually consider modeling cost as a joint PMF over `(clock, comm)`.
  This could capture random round and communication counts, preserving their
  correlation, to support protocols analyzed by expected rounds and expected
  communication. This is an exploratory idea, not a planned task.
