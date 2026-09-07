import Weft.PMF
import Weft.Std.Arith

/-!
# Randomised functionalities

Programs request randomness through functionalities:
uniform shares, nonzero shares, public coins and preprocessing correlations.
Each request samples fresh coins in `PMF`.
`seqUniform_eq_uniform` relates sequential draws to joint uniform sampling.

Evaluation models fix the coins to chosen values.
They describe that fixed execution;
for reactive programs, other coin choices may change both outputs and costs.
-/
namespace Weft

/-! ## A fresh random share -/

namespace Rand
inductive Op where | rand
abbrev ops (F : Type) : Interface where
  Op := Op
  dom _ := []
  cod _ := .share F
noncomputable def model (F : Type) [Fintype F] [Nonempty F] : Model (ops F) .ideal PMF :=
  ⟨fun _ => (uniform F).map fun x => (x, ())⟩
def eval (F : Type) [Inhabited F] : Model (ops F) .ideal Id := ⟨fun _ => pure ((default : F), ())⟩
end Rand

/-- Sample a uniform value and return it as a share. -/
abbrev Rand (F : Type) [Fintype F] [Inhabited F] : Functionality :=
  ⟨Rand.ops F, Rand.eval F, (· = Rand.model F), Functionality.unique_eq _⟩

@[simp, weft] theorem Rand.model_eq (F : Type) [Fintype F] [Inhabited F] :
    (Rand F).model = Rand.model F := Functionality.model_eq rfl

/-! ## Nonzero random shares -/

instance {F : Type} [Zero F] [Nontrivial F] : Nonempty {x : F // x ≠ 0} :=
  let ⟨x, hx⟩ := exists_ne (0 : F); ⟨⟨x, hx⟩⟩

namespace RandNZ
inductive Op where | randNZ
abbrev ops (F : Type) : Interface where
  Op := Op
  dom _ := []
  cod _ := .share F
noncomputable def model (F : Type) [Zero F] [Nontrivial F] [Fintype F] [DecidableEq F] : Model (ops F) .ideal PMF :=
  ⟨fun _ => (uniform {x : F // x ≠ 0}).map fun x => (x.1, ())⟩
def eval (F : Type) [One F] : Model (ops F) .ideal Id := ⟨fun _ => pure ((1 : F), ())⟩
end RandNZ

/-- Sample uniformly from `F \ {0}` and return a share.
Over a field, this supplies an invertible mask. -/
abbrev RandNZ (F : Type) [Zero F] [One F] [Nontrivial F] [Fintype F] [DecidableEq F] : Functionality :=
  ⟨RandNZ.ops F, RandNZ.eval F, (· = RandNZ.model F), Functionality.unique_eq _⟩

@[simp, weft] theorem RandNZ.model_eq (F : Type) [Zero F] [One F] [Nontrivial F] [Fintype F] [DecidableEq F] :
    (RandNZ F).model = RandNZ.model F := Functionality.model_eq rfl

/-! ## Public coins -/

namespace PubCoin
inductive Op where | coin
abbrev ops (F : Type) : Interface where
  Op := Op
  dom _ := []
  cod _ := .clear F
noncomputable def model (F : Type) [Fintype F] [Nonempty F] : Model (ops F) .ideal PMF :=
  ⟨fun _ => (uniform F).map fun x => (x, ())⟩
def eval (F : Type) [Inhabited F] : Model (ops F) .ideal Id := ⟨fun _ => pure ((default : F), ())⟩
end PubCoin

/-- Sample a uniform clear value, recorded in the event. -/
abbrev PubCoin (F : Type) [Fintype F] [Inhabited F] : Functionality :=
  ⟨PubCoin.ops F, PubCoin.eval F, (· = PubCoin.model F), Functionality.unique_eq _⟩

@[simp, weft] theorem PubCoin.model_eq (F : Type) [Fintype F] [Inhabited F] :
    (PubCoin F).model = PubCoin.model F := Functionality.model_eq rfl

/-! ## Correlated randomness -/

/-- A deterministic function of `k` jointly uniform coins. -/
structure Correlation (R T : Type) where
  k : Nat
  build : (Fin k → R) → T

/-- Apply the correlation function to a uniform draw from `Rᵏ`. -/
noncomputable def Correlation.sample {R T : Type} [Fintype R] [Nonempty R] (c : Correlation R T) : PMF T :=
  (uniform (Fin c.k → R)).map c.build

/-! ### A multiplication (Beaver) triple `(a, b, a·b)` -/
namespace MulTriple
inductive Op where | get
abbrev ops (F : Type) : Interface where
  Op := Op
  dom _ := []
  cod _ := .prod (.share F) (.prod (.share F) (.share F))
def corr (F : Type) [Mul F] : Correlation F (F × F × F) := ⟨2, fun x => (x 0, x 1, x 0 * x 1)⟩
noncomputable def model (F : Type) [Mul F] [Fintype F] [Nonempty F] : Model (ops F) .ideal PMF :=
  ⟨fun _ => (corr F).sample.map fun t => (t, ())⟩
def eval (F : Type) [Mul F] [Inhabited F] : Model (ops F) .ideal Id :=
  ⟨fun _ => pure (((default : F), (default : F), (default : F) * default), ())⟩
end MulTriple

/-- Sample `(a, b, a·b)` with independent uniform `a` and `b`. -/
abbrev MulTriple (F : Type) [Mul F] [Fintype F] [Inhabited F] : Functionality :=
  ⟨MulTriple.ops F, MulTriple.eval F, (· = MulTriple.model F), Functionality.unique_eq _⟩

@[simp, weft] theorem MulTriple.model_eq (F : Type) [Mul F] [Fintype F] [Inhabited F] :
    (MulTriple F).model = MulTriple.model F := Functionality.model_eq rfl

/-! ### A square pair `(r, r²)` -/
namespace SquarePair
inductive Op where | get
abbrev ops (F : Type) : Interface where
  Op := Op
  dom _ := []
  cod _ := .prod (.share F) (.share F)
def corr (F : Type) [Mul F] : Correlation F (F × F) := ⟨1, fun x => (x 0, x 0 * x 0)⟩
noncomputable def model (F : Type) [Mul F] [Fintype F] [Nonempty F] : Model (ops F) .ideal PMF :=
  ⟨fun _ => (corr F).sample.map fun t => (t, ())⟩
def eval (F : Type) [Mul F] [Inhabited F] : Model (ops F) .ideal Id :=
  ⟨fun _ => pure (((default : F), (default : F) * default), ())⟩
end SquarePair

/-- Sample `(r, r²)` with uniform `r`. -/
abbrev SquarePair (F : Type) [Mul F] [Fintype F] [Inhabited F] : Functionality :=
  ⟨SquarePair.ops F, SquarePair.eval F, (· = SquarePair.model F), Functionality.unique_eq _⟩

@[simp, weft] theorem SquarePair.model_eq (F : Type) [Mul F] [Fintype F] [Inhabited F] :
    (SquarePair F).model = SquarePair.model F := Functionality.model_eq rfl

/-! ### Double sharings

Both components represent the same random value.
This interface does not distinguish sharing degrees. -/
namespace DoubleSharing
inductive Op where | get
abbrev ops (F : Type) : Interface where
  Op := Op
  dom _ := []
  cod _ := .prod (.share F) (.share F)
def corr (F : Type) : Correlation F (F × F) := ⟨1, fun x => (x 0, x 0)⟩
noncomputable def model (F : Type) [Fintype F] [Nonempty F] : Model (ops F) .ideal PMF :=
  ⟨fun _ => (corr F).sample.map fun t => (t, ())⟩
def eval (F : Type) [Inhabited F] : Model (ops F) .ideal Id := ⟨fun _ => pure (((default : F), (default : F)), ())⟩
end DoubleSharing

/-- Return two shares of the same uniform value. -/
abbrev DoubleSharing (F : Type) [Fintype F] [Inhabited F] : Functionality :=
  ⟨DoubleSharing.ops F, DoubleSharing.eval F, (· = DoubleSharing.model F), Functionality.unique_eq _⟩

@[simp, weft] theorem DoubleSharing.model_eq (F : Type) [Fintype F] [Inhabited F] :
    (DoubleSharing F).model = DoubleSharing.model F := Functionality.model_eq rfl

/-! ## Program operations -/

section Ops
variable {F : Type} {fs : Hybrid} {D : Domain}

/-- Request a random share of the explicitly supplied type `F`. -/
def rand (F : Type) [Fintype F] [Inhabited F] [Has (Rand F) fs] : Prog fs.ops D (D.share F) :=
  Prog.op (F := Rand F) ⟨.rand, ()⟩
def randNZ (F : Type) [Zero F] [One F] [Nontrivial F] [Fintype F] [DecidableEq F] [Has (RandNZ F) fs] :
    Prog fs.ops D (D.share F) :=
  Prog.op (F := RandNZ F) ⟨.randNZ, ()⟩
def coin (F : Type) [Fintype F] [Inhabited F] [Has (PubCoin F) fs] : Prog fs.ops D (D.clear F) :=
  Prog.op (F := PubCoin F) ⟨.coin, ()⟩
def mulTriple (F : Type) [Mul F] [Fintype F] [Inhabited F] [Has (MulTriple F) fs] :
    Prog fs.ops D (D.share F × D.share F × D.share F) :=
  Prog.op (F := MulTriple F) ⟨.get, ()⟩
def squarePair (F : Type) [Mul F] [Fintype F] [Inhabited F] [Has (SquarePair F) fs] :
    Prog fs.ops D (D.share F × D.share F) :=
  Prog.op (F := SquarePair F) ⟨.get, ()⟩
def doubleSharing (F : Type) [Fintype F] [Inhabited F] [Has (DoubleSharing F) fs] :
    Prog fs.ops D (D.share F × D.share F) :=
  Prog.op (F := DoubleSharing F) ⟨.get, ()⟩

end Ops

end Weft
