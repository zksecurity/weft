import Weft.Shape

/-!
# Interfaces, requests and events

An interface specifies operations, operand and response shapes,
and a disclosure type for each operation.
A request supplies the operands of one operation.

An event records the operation and the model's declared disclosure.
Each model specifies what it discloses, including any public operands or responses.
The interpreter does not infer disclosure from operand or response shapes.
-/
namespace Weft

/-- The input, response and disclosure types of a single operation. -/
structure Signature where
  dom : List Shape
  cod : Shape
  leak : Type := Unit

/-- The operands of a single operation in a domain. -/
abbrev Signature.Args (σ : Signature) (D : Domain) : Type := Operands D σ.dom

/-- The response of a single operation in a domain. -/
abbrev Signature.Resp (σ : Signature) (D : Domain) : Type := σ.cod.interp D

/-- Operations with operand shapes, response shapes and disclosure types.
The model supplies the disclosure value; `Unit` denotes no value disclosure. -/
structure Interface where
  Op : Type
  dom : Op → List Shape
  cod : Op → Shape
  leak : Op → Type := fun _ => Unit

/-- The response type of an operation in a domain. -/
abbrev Resp (ι : Interface) (D : Domain) (o : ι.Op) : Type := (ι.cod o).interp D

/-- A request: an operation applied to operands. -/
structure Req (ι : Interface) (D : Domain) where
  op : ι.Op
  args : Operands D (ι.dom op)

/-- The adversary's record of a request: its operation and declared disclosure. -/
structure Event (ι : Interface) where
  op : ι.Op
  leak : ι.leak op

end Weft
