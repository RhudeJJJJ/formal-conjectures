import Proofs.JiaSong.Full
import Lean.Util.CollectAxioms

/-! Exact original full target equality, standard transitive axioms and negative controls. -/

open Lean Meta Elab Command in
run_elab do
  let original := `JiaSong.conjecture3_8
  let certificate := `JiaSong.full_conjecture3_8
  let oi ← getConstInfo original
  let ci ← getConstInfo certificate
  unless oi.levelParams.length == ci.levelParams.length do
    throwError "Universe-parameter mismatch"
  let levels := oi.levelParams.map Level.param
  let originalType ← inferType (mkConst original levels)
  unless ← isDefEq originalType (← inferType (mkConst certificate levels)) do
    throwError "The certificate changes the complete original target type"
  logInfo m!"EXACT TYPE: {original} = {certificate}"
  if ← isDefEq originalType (mkConst ``False) then
    throwError "Changed proposition accepted"
  logInfo "NEGATIVE CONTROL: changed proposition rejected"

#print axioms JiaSong.full_conjecture3_8
#print axioms JiaSong.Certificate.remoteness_value
#print axioms JiaSong.Certificate.ordered_spectrum
#print axioms JiaSong.conjecture3_8
