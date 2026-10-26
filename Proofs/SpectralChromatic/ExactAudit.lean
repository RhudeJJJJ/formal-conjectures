import Proofs.SpectralChromatic.Full
import Lean.Util.CollectAxioms

/-! Exact original-type equality and transitive axiom checks. -/

open Lean Meta Elab Command in
run_elab do
  let original := `AouchicheHansenStevanovic.SpectralChromatic.table1_upper
  let certificate := `AouchicheHansenStevanovic.SpectralChromatic.full_table1_upper
  let oi ← getConstInfo original
  let ci ← getConstInfo certificate
  unless oi.levelParams.length == ci.levelParams.length do
    throwError "Universe-parameter mismatch"
  let levels := oi.levelParams.map Level.param
  unless ← isDefEq (← inferType (mkConst original levels))
      (← inferType (mkConst certificate levels)) do
    throwError "Full target type differs from original"
  logInfo m!"EXACT TYPE: {original} = {certificate}"
  if ← isDefEq (← inferType (mkConst original levels)) (mkConst ``False) then
    throwError "Changed proposition was accepted"
  logInfo "NEGATIVE CONTROL: changed proposition rejected"

#print axioms AouchicheHansenStevanovic.SpectralChromatic.full_table1_upper
#print axioms AouchicheHansenStevanovic.SpectralChromatic.table1_upper
