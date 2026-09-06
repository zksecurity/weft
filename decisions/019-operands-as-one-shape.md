# 019 — The operands of an operation are one shape

## Question
`Interface.dom : Op → List Shape` gave an operation a list of operand
shapes and `Operands D ss` the corresponding tuple type, ending in `()`:
a binary operation took `(a, b, ())`, a unary one `(x, ())`, and the
response side, `cod : Op → Shape`, took a single shape.  Is the list
carrying anything, and can a user name the type of an operand?

## Choice
`dom : Op → Shape`, like `cod`.  Several operands are a product
(`.share F ⊗ .share F`, `⊗` being `Shape.prod`, right-associative), no
operand is `.unit`, a request's operands are one value of that shape
(`Args ι D o := (ι.dom o).interp D`), and `Operands` with its four
helpers is gone.  A binary operation now takes `(a, b)`, a unary one
takes `x`, and a shape is a Lean value, so an operand type has a name
when the author wants one:

```lean
abbrev Word          : Shape := .vec 32 (.share GF2)
abbrev ChainingValue : Shape := .vec 8 Word
abbrev Block         : Shape := .vec 16 Word
abbrev ops : Interface where
  Op := Op
  dom _ := ChainingValue ⊗ Block
  cod _ := ChainingValue
```

## Why
The list bought nothing.  `Operands D [a, b]` was definitionally
`a.interp D × b.interp D × Unit`, that is `Shape.prod a (Shape.prod b .unit)`,
and `blank`, `ready`, `untime` and `retime` on shapes already handled
products; the list was a holdover from when operands were shares only
(`dom : Op → List Type`, decision 014) and only the interface's two sides
were asymmetric.  With one shape on each side the same named shape serves
as an operand and as a response, and the record of a request is the
blank of one value on each side, `(ι.dom o).blank` beside `(ι.cod o).blank`.

## Alternatives
* **A Lean type as the payload of one share** (`.share ChainingValue`
  with `structure ChainingValue`).  Always possible, `Shape.share` takes
  any type, and right for a value a program only passes along: it is one
  opaque share with one ready time, which no domain-generic program can
  take apart.  A named *shape* keeps the bit-level structure, so the
  caller or a realisation can still feed the words to `Lin GF2`, and
  timing is per share.  Both remain available; they mean different things.
* **Keep the list and add a tuple helper** (`Shape.tuple : List Shape → Shape`).
  Rejected: it reintroduces the list at the surface, and the product
  notation reads as well.

## Consequences
Every model pattern lost its trailing `()`, every unary operand its
wrapping pair, every nullary `dom` became `.unit`; simulator records and
expected views shrank by one component per operation.  No proof changed
beyond those patterns.  The note that pairs are taken apart by projections
rather than patterns, to keep evaluation by `rfl` linear, now sits on
`Shape.blank` and applies to products as it did to the list.
