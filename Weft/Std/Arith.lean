import Weft.Init
import Weft.MPC

/-!
# The arithmetic functionalities

Each functionality is an interface (an inductive of operations, an operand
shape and a response shape for each) and a model.  Deterministic ones are
given at `Id` and lifted.  The name is the promise: `Mult.eval` says that
`mult` multiplies, and every hybrid that lists `Mult F` means that.

A functionality has no cost: an MPC prices it (`(Mult F).priced ⟨1, 2⟩`,
`Weft.MPC`).
-/
namespace Weft

/-! ## Linear operations: free and silent everywhere -/

namespace Lin
/-- Constants and scalars are clear operands: in the record of the request, by shape. -/
inductive Op where
  | const
  | add
  | sub
  | smul

abbrev ops (F : Type) : Interface where
  Op := Op
  dom | .const => .clear F | .add => .share F ⊗ .share F | .sub => .share F ⊗ .share F | .smul => .clear F ⊗ .share F
  cod _ := .share F
def eval (F : Type) [Add F] [Mul F] [Sub F] : Model (ops F) .ideal Id :=
  .silent fun
    | ⟨.const, c⟩ => c
    | ⟨.add, (a, b)⟩ => a + b
    | ⟨.sub, (a, b)⟩ => a - b
    | ⟨.smul, (c, a)⟩ => c * a
end Lin

/-- Linear operations. -/
abbrev Lin (F : Type) [Add F] [Mul F] [Sub F] : Functionality := .ofEval (Lin.ops F) (Lin.eval F)

@[simp, weft] theorem Lin.model_eq (F : Type) [Add F] [Mul F] [Sub F] :
    (Lin F).model = (Lin.eval F).lift PMF := Functionality.ofEval_model _ _

/-! ## Multiplication -/

namespace Mult
inductive Op where | mult
abbrev ops (F : Type) : Interface where
  Op := Op
  dom _ := .share F ⊗ .share F
  cod _ := .share F
def eval (F : Type) [Mul F] : Model (ops F) .ideal Id := .silent fun ⟨.mult, (a, b)⟩ => a * b
end Mult

/-- Secure multiplication. -/
abbrev Mult (F : Type) [Mul F] : Functionality := .ofEval (Mult.ops F) (Mult.eval F)

@[simp, weft] theorem Mult.model_eq (F : Type) [Mul F] :
    (Mult F).model = (Mult.eval F).lift PMF := Functionality.ofEval_model _ _

/-! ## Opening a share: the response is clear, and that is the whole disclosure -/

namespace Reveal
inductive Op where | reveal
abbrev ops (F : Type) : Interface where
  Op := Op
  dom _ := .share F
  cod _ := .clear F
def eval (F : Type) : Model (ops F) .ideal Id := .silent fun ⟨.reveal, x⟩ => x
end Reveal

/-- Opening a share to everyone.  The value is public by shape; nothing
further is declared. -/
abbrev Reveal (F : Type) : Functionality := .ofEval (Reveal.ops F) (Reveal.eval F)

@[simp, weft] theorem Reveal.model_eq (F : Type) :
    (Reveal F).model = (Reveal.eval F).lift PMF := Functionality.ofEval_model _ _

/-! ## Comparison -/

namespace Cmp
inductive Op where | lt
abbrev ops (F : Type) : Interface where
  Op := Op
  dom _ := .share F ⊗ .share F
  cod _ := .share F
def eval (F : Type) [LT F] [DecidableRel (α := F) (· < ·)] [Zero F] [One F] : Model (ops F) .ideal Id :=
  .silent fun ⟨.lt, (a, b)⟩ => (if a < b then 1 else 0 : F)
end Cmp

/-- A comparison functionality some MPCs offer natively: `[a < b]` as a share. -/
abbrev Cmp (F : Type) [LT F] [DecidableRel (α := F) (· < ·)] [Zero F] [One F] : Functionality :=
  .ofEval (Cmp.ops F) (Cmp.eval F)

@[simp, weft] theorem Cmp.model_eq (F : Type) [LT F] [DecidableRel (α := F) (· < ·)] [Zero F] [One F] :
    (Cmp F).model = (Cmp.eval F).lift PMF := Functionality.ofEval_model _ _

/-! ## Native inversion -/

namespace Inversion
inductive Op where | inv
abbrev ops (F : Type) : Interface where
  Op := Op
  dom _ := .share F
  cod _ := .share F
def eval (F : Type) [Inv F] : Model (ops F) .ideal Id := .silent fun ⟨.inv, x⟩ => (x⁻¹ : F)
end Inversion

/-- Native field inversion (`0⁻¹ = 0`, as in Mathlib). -/
abbrev Inversion (F : Type) [Inv F] : Functionality := .ofEval (Inversion.ops F) (Inversion.eval F)

@[simp, weft] theorem Inversion.model_eq (F : Type) [Inv F] :
    (Inversion F).model = (Inversion.eval F).lift PMF := Functionality.ofEval_model _ _

/-! ## The operations, as a program writes them -/

section Ops
variable {F : Type} {fs : Hybrid} {D : Domain}

def const [Add F] [Mul F] [Sub F] [Has (Lin F) fs] (c : D.clear F) : Prog fs.ops D (D.share F) :=
  Prog.op (F := Lin F) ⟨.const, c⟩
def add [Add F] [Mul F] [Sub F] [Has (Lin F) fs] (a b : D.share F) : Prog fs.ops D (D.share F) :=
  Prog.op (F := Lin F) ⟨.add, (a, b)⟩
def sub [Add F] [Mul F] [Sub F] [Has (Lin F) fs] (a b : D.share F) : Prog fs.ops D (D.share F) :=
  Prog.op (F := Lin F) ⟨.sub, (a, b)⟩
def smul [Add F] [Mul F] [Sub F] [Has (Lin F) fs] (c : D.clear F) (a : D.share F) : Prog fs.ops D (D.share F) :=
  Prog.op (F := Lin F) ⟨.smul, (c, a)⟩
def mul [Mul F] [Has (Mult F) fs] (a b : D.share F) : Prog fs.ops D (D.share F) :=
  Prog.op (F := Mult F) ⟨.mult, (a, b)⟩
def reveal [Has (Reveal F) fs] (x : D.share F) : Prog fs.ops D (D.clear F) :=
  Prog.op (F := Reveal F) ⟨.reveal, x⟩
def lt [LT F] [DecidableRel (α := F) (· < ·)] [Zero F] [One F] [Has (Cmp F) fs] (a b : D.share F) :
    Prog fs.ops D (D.share F) :=
  Prog.op (F := Cmp F) ⟨.lt, (a, b)⟩
def nativeInv [Inv F] [Has (Inversion F) fs] (x : D.share F) : Prog fs.ops D (D.share F) :=
  Prog.op (F := Inversion F) ⟨.inv, x⟩

end Ops

end Weft
