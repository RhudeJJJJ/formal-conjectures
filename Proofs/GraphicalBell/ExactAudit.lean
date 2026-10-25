import Proofs.GraphicalBell.Full
import Lean.Util.CollectAxioms

open Lean Meta Elab Command in
run_elab do
  let pairs : Array (Name × Name) := #[
    (`PHOEG.GraphicalBell.coefficientwise, `PHOEG.GraphicalBell.full_coefficientwise),
    (`PHOEG.GraphicalBell.conjecture, `PHOEG.GraphicalBell.full_conjecture)]
  for (original, certificate) in pairs do
    let originalInfo ← getConstInfo original
    let certificateInfo ← getConstInfo certificate
    unless originalInfo.levelParams.length == certificateInfo.levelParams.length do
      throwError "Universe-parameter mismatch: {original} and {certificate}"
    let levels := originalInfo.levelParams.map Level.param
    let a := mkConst original levels
    let b := mkConst certificate levels
    let ta ← inferType a
    let tb ← inferType b
    unless ← isDefEq ta tb do
      throwError "Target mismatch: {original} and {certificate}"
    logInfo m!"EXACT TYPE: {original} = {certificate}"

#print axioms PHOEG.GraphicalBell.full_coefficientwise
#print axioms PHOEG.GraphicalBell.full_conjecture
#print axioms PHOEG.GraphicalBell.coefficientwise
#print axioms PHOEG.GraphicalBell.conjecture
