import Weft.Shape

/-!
# Interfaces, requests and events

An *interface* is a vocabulary: the public operations, the shapes of the
operands of each, and the shape of its response.  A *request* is an
operation applied to operands; a clear operand (a public constant, a
scalar, an opened value) is a clear shape, a secret input is a share.

The adversary's record of one request, the *event*, has four channels:
the operation (public, it is the program), the clear operands and the
clear outputs (public, by shape), and the disclosure the functionality
declares.  The first three are structural: nothing user-written decides
what the adversary sees of a request, and a model cannot omit a public
value.
-/
namespace Weft

/-- An interface: operations with their operand shapes and response shapes.
`leak` is the *type* of the declared disclosure of an operation (`Unit`
when it declares nothing); what is disclosed is the model's business. -/
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

/-- The adversary's record of one request: the operation, the clear part of
the operands, the clear part of the response, the declared disclosure. -/
structure Event (ι : Interface) where
  op : ι.Op
  args : Operands .erased (ι.dom op)
  out : Resp ι .erased op
  leak : ι.leak op

end Weft
