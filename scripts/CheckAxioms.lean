import Weft
import Examples
import Lean.Util.CollectAxioms

/-! Check library and example declarations by their defining module, including
private declarations and axioms reached through imported dependencies. -/

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let moduleNames := env.header.moduleNames
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in env.constants.toList do
    let some moduleIdx := env.getModuleIdxFor? name | continue
    let moduleName := moduleNames[moduleIdx.toNat]!
    unless [`Weft, `Examples].any (·.isPrefixOf moduleName) do continue
    for axiomName in (← Lean.collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name} (from {moduleName}) depends on disallowed axiom {axiomName}"
    checked := checked + 1
  if checked == 0 then
    throwError "No library or example declarations were checked"
  logInfo m!"Checked axioms of {checked} library and example declarations."
