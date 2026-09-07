import Lean

/-!
# Semantic simplification

`weft` collects interpreter laws, transport rules for `Has`,
and standard functionality models.
`simp [weft, myProgram]` unfolds a concrete run into random draws and a result.
-/

/-- Equations for unfolding program semantics. -/
register_simp_attr weft
