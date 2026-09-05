import Weft.Init
import Weft.Functionality
import Weft.Timed

/-!
# The arithmetic functionalities

Each functionality is an interface (an inductive of operations, the clear
arguments in the constructors, operand lists, response shapes) and a
model.  Deterministic ones are given at `Id` and lifted.  The name is the
promise: `Mult.ideal` says that `mult` multiplies, and every hybrid that
lists `Mult F` means that.
-/
namespace Weft

/-! ## Linear operations: free and silent everywhere -/

namespace Lin
/-- Constants and scalars are clear arguments, so they are part of the operation. -/
inductive Op (F : Type) where
  | const (c : F)
  | add
  | sub
  | smul (c : F)

abbrev ops (F : Type) : Interface where
  Op := Op F
  dom | .const _ => [] | .add => [F, F] | .sub => [F, F] | .smul _ => [F]
  cod _ := .share F
  pubArg | .const _ => true | .smul _ => true | _ => false

def eval (F : Type) [Add F] [Mul F] [Sub F] : Model (ops F) .ideal Id :=
  .silent fun
    | ⟨.const c, ()⟩ => c
    | ⟨.add, (a, b, ())⟩ => a + b
    | ⟨.sub, (a, b, ())⟩ => a - b
    | ⟨.smul c, (a, ())⟩ => c * a
/-- Free, ready when the operands are; an operation with a clear argument
also waits for the reveal clock, since clear computation is opaque. -/
def timed (F : Type) [Add F] [Mul F] [Sub F] (ℓ : Op F → Nat) : Model (ops F) .timed Sched :=
  ⟨fun r s => match r with
    | ⟨.const c, ()⟩ => ((⟨c, max s.clock s.revealed + ℓ (.const c)⟩, ()), s)
    | ⟨.add, (a, b, ())⟩ => ((⟨a.val + b.val, max a.time (max b.time s.clock) + ℓ .add⟩, ()), s)
    | ⟨.sub, (a, b, ())⟩ => ((⟨a.val - b.val, max a.time (max b.time s.clock) + ℓ .sub⟩, ()), s)
    | ⟨.smul c, (a, ())⟩ => ((⟨c * a.val, max a.time (max s.clock s.revealed) + ℓ (.smul c)⟩, ()), s)⟩
end Lin

/-- Linear operations. -/
abbrev Lin (F : Type) [Add F] [Mul F] [Sub F] : Functionality := .ofEval (Lin.ops F) (Lin.eval F) (Lin.timed F)

@[simp, weft] theorem Lin.model_eq (F : Type) [Add F] [Mul F] [Sub F] :
    (Lin F).model = (Lin.eval F).lift PMF := Functionality.ofEval_model _ _ _

/-! ## Multiplication -/

namespace Mult
inductive Op where | mult
abbrev ops (F : Type) : Interface where
  Op := Op
  dom _ := [F, F]
  cod _ := .share F
def eval (F : Type) [Mul F] : Model (ops F) .ideal Id := .silent fun ⟨.mult, (a, b, ())⟩ => a * b
def timed (F : Type) [Mul F] (ℓ : Op → Nat) : Model (ops F) .timed Sched :=
  ⟨fun r s => match r with
    | ⟨.mult, (a, b, ())⟩ => ((⟨a.val * b.val, max a.time (max b.time s.clock) + ℓ .mult⟩, ()), s)⟩
end Mult

/-- Secure multiplication. -/
abbrev Mult (F : Type) [Mul F] : Functionality := .ofEval (Mult.ops F) (Mult.eval F) (Mult.timed F)

@[simp, weft] theorem Mult.model_eq (F : Type) [Mul F] :
    (Mult F).model = (Mult.eval F).lift PMF := Functionality.ofEval_model _ _ _

/-! ## Opening a share: the response is clear, and that is the whole disclosure -/

namespace Reveal
inductive Op where | reveal
abbrev ops (F : Type) : Interface where
  Op := Op
  dom _ := [F]
  cod _ := .clear F
def eval (F : Type) : Model (ops F) .ideal Id := .silent fun ⟨.reveal, (x, ())⟩ => x
/-- The value is clear `ℓ` later, and the reveal clock records when.
Independent reveals stay in the same round; only a barrier serialises what
follows. -/
def timed (F : Type) (ℓ : Op → Nat) : Model (ops F) .timed Sched :=
  ⟨fun r s => match r with
    | ⟨.reveal, (x, ())⟩ =>
      let t := max x.time s.clock + ℓ .reveal
      ((x.val, ()), { s with revealed := max s.revealed t })⟩
end Reveal

/-- Opening a share to everyone.  The value is public by shape; nothing
further is declared. -/
abbrev Reveal (F : Type) : Functionality := .ofEval (Reveal.ops F) (Reveal.eval F) (Reveal.timed F)

@[simp, weft] theorem Reveal.model_eq (F : Type) :
    (Reveal F).model = (Reveal.eval F).lift PMF := Functionality.ofEval_model _ _ _

/-! ## Comparison -/

namespace Cmp
inductive Op where | lt
abbrev ops (F : Type) : Interface where
  Op := Op
  dom _ := [F, F]
  cod _ := .share F
def eval (F : Type) [LT F] [DecidableRel (α := F) (· < ·)] [Zero F] [One F] : Model (ops F) .ideal Id :=
  .silent fun ⟨.lt, (a, b, ())⟩ => (if a < b then 1 else 0 : F)
def timed (F : Type) [LT F] [DecidableRel (α := F) (· < ·)] [Zero F] [One F] (ℓ : Op → Nat) :
    Model (ops F) .timed Sched :=
  ⟨fun r s => match r with
    | ⟨.lt, (a, b, ())⟩ => ((⟨(if a.val < b.val then 1 else 0 : F), max a.time (max b.time s.clock) + ℓ .lt⟩, ()), s)⟩
end Cmp

/-- A comparison functionality some MPCs offer natively: `[a < b]` as a share. -/
abbrev Cmp (F : Type) [LT F] [DecidableRel (α := F) (· < ·)] [Zero F] [One F] : Functionality :=
  .ofEval (Cmp.ops F) (Cmp.eval F) (Cmp.timed F)

@[simp, weft] theorem Cmp.model_eq (F : Type) [LT F] [DecidableRel (α := F) (· < ·)] [Zero F] [One F] :
    (Cmp F).model = (Cmp.eval F).lift PMF := Functionality.ofEval_model _ _ _

/-! ## Native inversion -/

namespace Inversion
inductive Op where | inv
abbrev ops (F : Type) : Interface where
  Op := Op
  dom _ := [F]
  cod _ := .share F
def eval (F : Type) [Inv F] : Model (ops F) .ideal Id := .silent fun ⟨.inv, (x, ())⟩ => (x⁻¹ : F)
def timed (F : Type) [Inv F] (ℓ : Op → Nat) : Model (ops F) .timed Sched :=
  ⟨fun r s => match r with
    | ⟨.inv, (x, ())⟩ => ((⟨(x.val⁻¹ : F), max x.time s.clock + ℓ .inv⟩, ()), s)⟩
end Inversion

/-- Native field inversion (`0⁻¹ = 0`, as in Mathlib). -/
abbrev Inversion (F : Type) [Inv F] : Functionality := .ofEval (Inversion.ops F) (Inversion.eval F) (Inversion.timed F)

@[simp, weft] theorem Inversion.model_eq (F : Type) [Inv F] :
    (Inversion F).model = (Inversion.eval F).lift PMF := Functionality.ofEval_model _ _ _

/-! ## A control barrier -/

namespace Barrier
inductive Op where | barrier
abbrev ops : Interface where
  Op := Op
  dom _ := []
  cod _ := .unit
  ctrl _ := true
def eval : Model ops .ideal Id := .silent fun _ => ()
/-- Raise the control clock to the reveal clock. -/
def timed (_ : Op → Nat) : Model ops .timed Sched :=
  ⟨fun _ s => (((), ()), { s with clock := max s.clock s.revealed })⟩
end Barrier

/-- A control dependency: the program is about to branch on revealed
values.  Semantically a no-op; in the timed domain it raises the control
clock to the reveal clock, so everything issued afterwards is scheduled
after those values are known.  Straight-line code never needs it. -/
abbrev Barrier : Functionality := .ofEval Barrier.ops Barrier.eval Barrier.timed

@[simp, weft] theorem Barrier.model_eq : Barrier.model = Barrier.eval.lift PMF := Functionality.ofEval_model _ _ _

/-! ## The operations, as a program writes them -/

section Ops
variable {F : Type} {fs : Hybrid} {D : Domain}

def const [Add F] [Mul F] [Sub F] [Has (Lin F) fs] (c : F) : Prog fs.ops D (D.sh F) :=
  Prog.op (F := Lin F) ⟨.const c, ()⟩
def add [Add F] [Mul F] [Sub F] [Has (Lin F) fs] (a b : D.sh F) : Prog fs.ops D (D.sh F) :=
  Prog.op (F := Lin F) ⟨.add, (a, b, ())⟩
def sub [Add F] [Mul F] [Sub F] [Has (Lin F) fs] (a b : D.sh F) : Prog fs.ops D (D.sh F) :=
  Prog.op (F := Lin F) ⟨.sub, (a, b, ())⟩
def smul [Add F] [Mul F] [Sub F] [Has (Lin F) fs] (c : F) (a : D.sh F) : Prog fs.ops D (D.sh F) :=
  Prog.op (F := Lin F) ⟨.smul c, (a, ())⟩
def mul [Mul F] [Has (Mult F) fs] (a b : D.sh F) : Prog fs.ops D (D.sh F) :=
  Prog.op (F := Mult F) ⟨.mult, (a, b, ())⟩
def reveal [Has (Reveal F) fs] (x : D.sh F) : Prog fs.ops D F :=
  Prog.op (F := Reveal F) ⟨.reveal, (x, ())⟩
def lt [LT F] [DecidableRel (α := F) (· < ·)] [Zero F] [One F] [Has (Cmp F) fs] (a b : D.sh F) :
    Prog fs.ops D (D.sh F) :=
  Prog.op (F := Cmp F) ⟨.lt, (a, b, ())⟩
def nativeInv [Inv F] [Has (Inversion F) fs] (x : D.sh F) : Prog fs.ops D (D.sh F) :=
  Prog.op (F := Inversion F) ⟨.inv, (x, ())⟩
def barrier [Has Barrier fs] : Prog fs.ops D Unit :=
  Prog.op (F := Barrier) ⟨.barrier, ()⟩

end Ops

end Weft
