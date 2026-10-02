import Weft.Init
import Weft.MPC

/-!
# Arithmetic functionalities

Each functionality has one operation with a fixed input/output/leakage signature.
Constants and scalar multiplication explicitly disclose their public operands;
reveal returns and discloses its opened value.
-/
namespace Weft

namespace Const
abbrev sig (F : Type) : Signature := ⟨[.clear F], .share F, F⟩
def eval (F : Type) : FunctionModel (sig F) .ideal Id := ⟨fun (c, ()) => pure (c, c)⟩
end Const

/-- Share a public constant and disclose that constant. -/
abbrev Const (F : Type) : Functionality := .ofEval (Const.sig F) (Const.eval F)
@[simp, weft] theorem Const.model_eq (F : Type) : (Const F).model = (Const.eval F).lift PMF :=
  Functionality.ofEval_model _ _

namespace Addition
abbrev sig (F : Type) : Signature := ⟨[.share F, .share F], .share F, Unit⟩
def eval (F : Type) [Add F] : FunctionModel (sig F) .ideal Id :=
  ⟨fun (a, b, ()) => pure (a + b, ())⟩
end Addition

/-- Add two shares without value disclosure. -/
abbrev Addition (F : Type) [Add F] : Functionality := .ofEval (Addition.sig F) (Addition.eval F)
@[simp, weft] theorem Addition.model_eq
    (F : Type)
    [Add F] :
    (Addition F).model = (Addition.eval F).lift PMF :=
  Functionality.ofEval_model _ _

namespace Subtraction
abbrev sig (F : Type) : Signature := ⟨[.share F, .share F], .share F, Unit⟩
def eval (F : Type) [Sub F] : FunctionModel (sig F) .ideal Id :=
  ⟨fun (a, b, ()) => pure (a - b, ())⟩
end Subtraction

/-- Subtract two shares without value disclosure. -/
abbrev Subtraction
    (F : Type)
    [Sub F] :
    Functionality := .ofEval (Subtraction.sig F) (Subtraction.eval F)
@[simp, weft] theorem Subtraction.model_eq
    (F : Type)
    [Sub F] :
    (Subtraction F).model = (Subtraction.eval F).lift PMF :=
  Functionality.ofEval_model _ _

namespace Smul
abbrev sig (F : Type) : Signature := ⟨[.clear F, .share F], .share F, F⟩
def eval (F : Type) [Mul F] : FunctionModel (sig F) .ideal Id := ⟨fun (c, a, ()) => pure (c * a, c)⟩
end Smul

/-- Multiply a share by a public scalar and disclose the scalar. -/
abbrev Smul (F : Type) [Mul F] : Functionality := .ofEval (Smul.sig F) (Smul.eval F)
@[simp, weft] theorem Smul.model_eq (F : Type) [Mul F] : (Smul F).model = (Smul.eval F).lift PMF :=
  Functionality.ofEval_model _ _

namespace Mult
abbrev sig (F : Type) : Signature := ⟨[.share F, .share F], .share F, Unit⟩
def eval (F : Type) [Mul F] : FunctionModel (sig F) .ideal Id :=
  ⟨fun (a, b, ()) => pure (a * b, ())⟩
end Mult

/-- Multiply two shares without value disclosure. -/
abbrev Mult (F : Type) [Mul F] : Functionality := .ofEval (Mult.sig F) (Mult.eval F)
@[simp, weft] theorem Mult.model_eq (F : Type) [Mul F] : (Mult F).model = (Mult.eval F).lift PMF :=
  Functionality.ofEval_model _ _

namespace Reveal
abbrev sig (F : Type) : Signature := ⟨[.share F], .clear F, F⟩
def eval (F : Type) : FunctionModel (sig F) .ideal Id := ⟨fun (x, ()) => pure (x, x)⟩
end Reveal

/-- Return a share's value in the clear and explicitly disclose it. -/
abbrev Reveal (F : Type) : Functionality := .ofEval (Reveal.sig F) (Reveal.eval F)
@[simp, weft] theorem Reveal.model_eq (F : Type) : (Reveal F).model = (Reveal.eval F).lift PMF :=
  Functionality.ofEval_model _ _

namespace Cmp
abbrev sig (F : Type) : Signature := ⟨[.share F, .share F], .share F, Unit⟩
def eval
    (F : Type)
    [LT F]
    [DecidableRel (α := F) (· < ·)]
    [Zero F]
    [One F] :
    FunctionModel (sig F) .ideal Id :=
  ⟨fun (a, b, ()) => pure ((if a < b then 1 else 0 : F), ())⟩
end Cmp

/-- Return the shared indicator `[a < b]` without disclosure. -/
abbrev Cmp (F : Type) [LT F] [DecidableRel (α := F) (· < ·)] [Zero F] [One F] : Functionality :=
  .ofEval (Cmp.sig F) (Cmp.eval F)
@[simp, weft] theorem Cmp.model_eq
    (F : Type)
    [LT F]
    [DecidableRel (α := F) (· < ·)]
    [Zero F]
    [One F] :
    (Cmp F).model = (Cmp.eval F).lift PMF := Functionality.ofEval_model _ _

namespace Inversion
abbrev sig (F : Type) : Signature := ⟨[.share F], .share F, Unit⟩
def eval (F : Type) [Inv F] : FunctionModel (sig F) .ideal Id :=
  ⟨fun (x, ()) => pure ((x⁻¹ : F), ())⟩
end Inversion

/-- Return a shared inverse without disclosure. -/
abbrev Inversion (F : Type) [Inv F] : Functionality := .ofEval (Inversion.sig F) (Inversion.eval F)
@[simp, weft] theorem Inversion.model_eq (F : Type) [Inv F] :
    (Inversion F).model = (Inversion.eval F).lift PMF := Functionality.ofEval_model _ _

section Ops
variable {F : Type} {fs : Hybrid} {D : Domain}

def const
    [Has (Const F) fs]
    (c : D.clear F) :
    Prog fs.ops D (D.share F) := Prog.op (F := Const F) (c, ())
def add
    [Add F]
    [Has (Addition F) fs]
    (a b : D.share F) :
    Prog fs.ops D (D.share F) := Prog.op (F := Addition F) (a, b, ())
def sub
    [Sub F]
    [Has (Subtraction F) fs]
    (a b : D.share F) :
    Prog fs.ops D (D.share F) := Prog.op (F := Subtraction F) (a, b, ())
def smul
    [Mul F]
    [Has (Smul F) fs]
    (c : D.clear F)
    (a : D.share F) :
    Prog fs.ops D (D.share F) := Prog.op (F := Smul F) (c, a, ())
def mul
    [Mul F]
    [Has (Mult F) fs]
    (a b : D.share F) :
    Prog fs.ops D (D.share F) := Prog.op (F := Mult F) (a, b, ())
def reveal
    [Has (Reveal F) fs]
    (x : D.share F) :
    Prog fs.ops D (D.clear F) := Prog.op (F := Reveal F) (x, ())
def lt
    [LT F]
    [DecidableRel (α := F) (· < ·)]
    [Zero F]
    [One F]
    [Has (Cmp F) fs]
    (a b : D.share F) :
    Prog fs.ops D (D.share F) := Prog.op (F := Cmp F) (a, b, ())
def nativeInv
    [Inv F]
    [Has (Inversion F) fs]
    (x : D.share F) :
    Prog fs.ops D (D.share F) := Prog.op (F := Inversion F) (x, ())

end Ops
end Weft
