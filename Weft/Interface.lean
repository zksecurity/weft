import Weft.Shape

/-!
# Interfaces, requests and events

An *interface* is a vocabulary: the public operations (a constructor with
its clear arguments), the operand types of each, and the shape of its
response.  A *request* is an operation applied to share operands.

The adversary's record of one request, the *event*, has three channels:
the operation (public, it is the program), the clear outputs (public, by
shape), and the disclosure the functionality declares.  Operation and
clear outputs are structural: nothing user-written decides what the
adversary sees of a request, and a model cannot omit a public output.
-/
namespace Weft

/-- An interface: operations with their operand types and response shapes.
`leak` is the *type* of the declared disclosure of an operation (`Unit`
when it declares nothing); what is disclosed is the model's business.

`clearArg` and `barrier` are scheduling metadata for the timed domain,
trusted like the rest of the interface, and needed because clear values
carry no time: an operation whose constructor carries a clear argument
(`smul c`) may depend on any value opened before it, so it waits for the
reveal clock; a barrier is the operation a program issues before
branching on an opened value, so that what follows waits for it. -/
structure Interface where
  Op : Type
  dom : Op → List Type
  cod : Op → Shape
  leak : Op → Type := fun _ => Unit
  clearArg : Op → Bool := fun _ => false
  barrier : Op → Bool := fun _ => false

/-- The response type of an operation in a domain. -/
abbrev Resp (ι : Interface) (D : Domain) (o : ι.Op) : Type := (ι.cod o).interp D

/-- A request: an operation applied to share operands. -/
structure Req (ι : Interface) (D : Domain) where
  op : ι.Op
  args : Operands D (ι.dom op)

/-- The adversary's record of one request: the operation, the clear part of
the response, the declared disclosure. -/
structure Event (ι : Interface) where
  op : ι.Op
  out : Resp ι .erased op
  leak : ι.leak op

/-- An event with nothing declared. -/
abbrev Event.silent {ι : Interface} (o : ι.Op) (h : ι.leak o = Unit := by rfl)
    (out : Resp ι .erased o) : Event ι :=
  ⟨o, out, h ▸ ()⟩

end Weft
