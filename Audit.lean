import LectureNotes
import Lean.Util.CollectAxioms

/-! This command checks every declaration from every project module,
including private definitions and generated declarations. It follows proof
dependencies transitively and permits only Lean's standard logical axioms. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut checked : Nat := 0
  let mut theoremCount : Nat := 0
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let moduleName := env.header.moduleNames[idx.toNat]!
    unless (`LectureNotes).isPrefixOf moduleName do continue
    checked := checked + 1
    if info.isTheorem then theoremCount := theoremCount + 1
    if info.isAxiom then
      throwError "Project axiom is forbidden: {name}"
    let axioms ← collectAxioms name
    for axiomName in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "{name} depends on forbidden axiom {axiomName}"
  if checked == 0 then throwError "Audit found no project declarations"
  logInfo m!"Proof audit passed: {checked} declarations ({theoremCount} theorem declarations), no forbidden axioms."
