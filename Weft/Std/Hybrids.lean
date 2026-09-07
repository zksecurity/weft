import Weft.Std.Random

/-!
# Standard hybrids

`Std F` offers linear operations, multiplication and reveal.
`Pre F` offers linear operations, reveal and Beaver triples.
To run a `Std F` program over `Pre F`,
replace multiplication with its Beaver realisation (`Examples.Privacy`).
-/
namespace Weft

/-- Linear operations, multiplication and reveal. -/
abbrev Std (F : Type) [Add F] [Mul F] [Sub F] : Hybrid := [Lin F, Mult F, Reveal F]

namespace Std
variable (F : Type) [Add F] [Mul F] [Sub F]
/-- Component indices used when stating views. -/
abbrev lin (o : Lin.Op) : (Std F).ops.Op := ⟨0, o⟩
abbrev mult : (Std F).ops.Op := ⟨1, .mult⟩
abbrev reveal : (Std F).ops.Op := ⟨2, .reveal⟩
/-- Zero-cost linear operations with configurable multiplication and reveal prices.
The defaults are `(1 round, 2 units)` and `(1 round, 1 unit)`, respectively. -/
abbrev mpc (pMult : Price := ⟨1, 2⟩) (pReveal : Price := ⟨1, 1⟩) : MPC :=
  [(Lin F).priced ⟨0, 0⟩, (Mult F).priced pMult, (Reveal F).priced pReveal]
/-- Timed model of `Std` at the supplied prices. -/
def timed (pMult : Price := ⟨1, 2⟩) (pReveal : Price := ⟨1, 1⟩) : Model (Std F).ops .timed Sched :=
  (mpc F pMult pReveal).timed
end Std

/-- Linear operations, reveal and Beaver triples. -/
abbrev Pre (F : Type) [Add F] [Mul F] [Sub F] [Fintype F] [Inhabited F] : Hybrid :=
  [Lin F, Reveal F, MulTriple F]

namespace Pre
variable (F : Type) [Add F] [Mul F] [Sub F] [Fintype F] [Inhabited F]
abbrev lin (o : Lin.Op) : (Pre F).ops.Op := ⟨0, o⟩
abbrev reveal : (Pre F).ops.Op := ⟨1, .reveal⟩
abbrev triple : (Pre F).ops.Op := ⟨2, .get⟩
/-- Preprocessing MPC with zero-cost triples by default. -/
abbrev mpc (pReveal : Price := ⟨1, 1⟩) (pTriple : Price := ⟨0, 0⟩) : MPC :=
  [(Lin F).priced ⟨0, 0⟩, (Reveal F).priced pReveal, (MulTriple F).priced pTriple]
/-- Timed model of `Pre` at the supplied prices. -/
def timed (pReveal : Price := ⟨1, 1⟩) (pTriple : Price := ⟨0, 0⟩) : Model (Pre F).ops .timed Sched :=
  (mpc F pReveal pTriple).timed
end Pre

/-- A share available at round 0, for delay examples. -/
notation "⟪" x "⟫" => Timed.now x

end Weft

/-! ## Semantic simplification rules -/
namespace Weft
attribute [weft] Prog.bind_eq Prog.pure_eq Prog.bind_pure' Prog.bind_call Prog.bind_look Prog.handle_pure Prog.handle_call
  Prog.handle_look run_look_ideal dist_look Look.ideal_look Domain.ideal_map Domain.ideal_pure Domain.ideal_seq
  Prog.op_here Prog.op_there Prog.lift Prog.opHead
  dist_bind dist_call dist_pure dist_pure' Hybrid.model_cons_zero Hybrid.model_cons_succ
  Model.det_step Model.lift_step Model.silent Model.det Model.program Id.run_pure
  PMF.monad_bind_eq_bind PMF.monad_pure_eq_pure PMF.monad_map_eq_map
  PMF.map_bind PMF.pure_map PMF.bind_map PMF.bind_bind PMF.pure_bind PMF.bind_pure
  PMF.bind_const Function.comp_def
  Shape.blank_share Shape.blank_clear Shape.blank_unit Shape.blank_prod Shape.blank_vec Shape.blank_list
  Operands.blank_nil Operands.blank_cons
  Correlation.sample
  Lin.eval Mult.eval Reveal.eval Cmp.eval Inversion.eval
  Rand.model RandNZ.model PubCoin.model MulTriple.model SquarePair.model DoubleSharing.model
  MulTriple.corr SquarePair.corr DoubleSharing.corr
end Weft
