import Proofs.Byzov.Full
import Lean.Util.CollectAxioms

/-! Exact original target-type equality, transitive axioms and negative controls. -/

open Lean Meta Elab Command in
run_elab do
  let original := `ByzovPushkarev.conjecture8
  let certificate := `ByzovPushkarev.full_conjecture8
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

#print axioms ByzovPushkarev.full_conjecture8
#print axioms ByzovPushkarev.Certificate.profiles_determine_canon
#print axioms ByzovPushkarev.Certificate.tournament_rotation
#print axioms ByzovPushkarev.Certificate.parameterAut_surjective
#print axioms ByzovPushkarev.conjecture8
