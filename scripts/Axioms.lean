module

import PushFS
import all Lean.Util.CollectAxioms

/-! Audit PushFS and its NCL source against Lean's three standard axioms. -/

run_cmd do
  let env ← Lean.getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let imported := Lean.exportedAxiomsExt.getState (asyncMode := .mainOnly) env
  let checked := Lean.CollectAxioms.runM (env.setExporting false) do
    let mut checked := #[]
    for (name, _) in env.constants.toList do
      if (`PushPuzzle).isPrefixOf name then
        checked := checked.push (name, ← Lean.CollectAxioms.collectAndGet imported.find? name)
    return checked
  for (name, axioms) in checked do
    for ax in axioms do
      unless allowed.contains ax do
        throwError "{name} depends on unapproved axiom {ax}"
  Lean.logInfo m!"Audited {checked.size} declarations in the PushFS environment."
