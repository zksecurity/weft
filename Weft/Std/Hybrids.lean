import Weft.Std.Random

/-!
# Standard hybrids

`Std F` is the arithmetic black box; `Pre F` is a preprocessing model with
no native multiplication.  Both are lists, and a program written against
`[Has (Lin F) fs] [Has (Mult F) fs]` runs on either, and on any other
hybrid that lists what it needs.
-/
namespace Weft

/-- The arithmetic black box. -/
abbrev Std (F : Type) [Add F] [Mul F] [Sub F] : Hybrid := [Lin F, Mult F, Reveal F]

namespace Std
variable (F : Type) [Add F] [Mul F] [Sub F]
/-- The operations of the black box, by position, for stating views. -/
abbrev lin (o : Lin.Op F) : (Std F).ops.Op := ⟨0, o⟩
abbrev mult : (Std F).ops.Op := ⟨1, .mult⟩
abbrev reveal : (Std F).ops.Op := ⟨2, .reveal⟩
/-- The black box as an MPC: linear operations free, multiplication one
round and two units, reveal one round and one unit, by default. -/
abbrev mpc (pMult : Price := ⟨1, 2⟩) (pReveal : Price := ⟨1, 1⟩) : MPC :=
  [(Lin F).priced ⟨0, 0⟩, (Mult F).priced pMult, (Reveal F).priced pReveal]
/-- The cost instantiation of the black box, at those prices. -/
def timed (pMult : Price := ⟨1, 2⟩) (pReveal : Price := ⟨1, 1⟩) : Model (Std F).ops .timed Sched :=
  (mpc F pMult pReveal).timed
end Std

/-- A preprocessing-model functionality: no native multiplication, Beaver triples instead. -/
abbrev Pre (F : Type) [Add F] [Mul F] [Sub F] [Fintype F] [Inhabited F] : Hybrid :=
  [Lin F, Reveal F, MulTriple F]

namespace Pre
variable (F : Type) [Add F] [Mul F] [Sub F] [Fintype F] [Inhabited F]
abbrev lin (o : Lin.Op F) : (Pre F).ops.Op := ⟨0, o⟩
abbrev reveal : (Pre F).ops.Op := ⟨1, .reveal⟩
abbrev triple : (Pre F).ops.Op := ⟨2, .get⟩
/-- The preprocessing model as an MPC: triples free when precomputed. -/
abbrev mpc (pReveal : Price := ⟨1, 1⟩) (pTriple : Price := ⟨0, 0⟩) : MPC :=
  [(Lin F).priced ⟨0, 0⟩, (Reveal F).priced pReveal, (MulTriple F).priced pTriple]
/-- The cost instantiation of the preprocessing model, at those prices. -/
def timed (pReveal : Price := ⟨1, 1⟩) (pTriple : Price := ⟨0, 0⟩) : Model (Pre F).ops .timed Sched :=
  (mpc F pReveal pTriple).timed
end Pre

/-- A share available at round 0, for delay examples. -/
notation "⟪" x "⟫" => Timed.now x

end Weft

/-! ## The simp set that unfolds a program's semantics -/
namespace Weft
attribute [weft] Prog.bind_eq Prog.pure_eq Prog.bind_pure' Prog.bind_call Prog.handle_pure Prog.handle_call
  Prog.op_here Prog.op_there Prog.lift Prog.opHead
  dist_bind dist_call dist_pure dist_pure' Hybrid.model_cons_zero Hybrid.model_cons_succ
  Model.det_step Model.lift_step Model.silent Model.det Model.program Id.run_pure
  PMF.monad_bind_eq_bind PMF.monad_pure_eq_pure PMF.monad_map_eq_map
  PMF.map_bind PMF.pure_map PMF.bind_map PMF.bind_bind PMF.pure_bind PMF.bind_pure
  PMF.bind_const Function.comp_def
  Shape.blank_share Shape.blank_clear Shape.blank_unit Shape.blank_prod Shape.blank_vec Shape.blank_list
  Correlation.sample
  Lin.eval Mult.eval Reveal.eval Cmp.eval Inversion.eval Barrier.eval
  Rand.model RandNZ.model PubCoin.model MulTriple.model SquarePair.model DoubleSharing.model
  MulTriple.corr SquarePair.corr DoubleSharing.corr
end Weft
