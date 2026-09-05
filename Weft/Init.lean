import Lean

/-!
# Simp sets

`weft` collects the equations that unfold the semantics of a concrete
program: the interpreter's laws, the transports along `Has`, and each
standard functionality's model.  `simp [weft, ‹the program›]` normalises
`dist fs.model c` to "draw the coins, then a point".
-/

/-- Unfolding the semantics of a concrete program. -/
register_simp_attr weft
