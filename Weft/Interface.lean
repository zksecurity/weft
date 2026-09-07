import Weft.Shape

/-!
# Interfaces, requests and events

An interface specifies operations, operand and response shapes,
and a disclosure type for each operation.
A request supplies the operands of one operation.

An event records the operation, clear operands, clear response components,
and the model's declared disclosure.
The interpreter derives the clear components from their shapes,
so they are recorded independently of the declared disclosure.
-/
namespace Weft

/-- Operations with operand shapes, response shapes and disclosure types.
The model supplies the disclosure value; `Unit` denotes no additional disclosure. -/
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

/-- The adversary's record of a request.
Shared operands and response components are erased;
clear components retain their representation in `D`. -/
structure Event (ι : Interface) (D : Domain := .ideal) where
  op : ι.Op
  args : Operands D.erase (ι.dom op)
  out : Resp ι D.erase op
  leak : ι.leak op

end Weft
