import FormalConjectures.WrittenOnTheWallII.GraphConjecture96
import Proofs.WOWII9684.Full96
import Lean.Util.CollectAxioms

open Lean Meta Elab Command in
run_elab do
  let original := `WrittenOnTheWallII.GraphConjecture96.conjecture96
  let certificate := `WOWII96.full_conjecture96
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

#print axioms WOWII96.full_conjecture96
#print axioms WOWII96.independent_bound
#print axioms WOWII96.local_card_bound
#print axioms WrittenOnTheWallII.GraphConjecture96.conjecture96
