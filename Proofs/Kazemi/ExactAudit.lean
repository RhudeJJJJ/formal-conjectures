import Proofs.Kazemi.Full
import Lean.Util.CollectAxioms

/-! Exact full target equality, transitive axiom audit and negative controls. -/

open Lean Meta Elab Command in
run_elab do
  let original := `Kazemi.Hypercube.conjecture6_1
  let certificate := `Kazemi.Hypercube.full_conjecture6_1
  let oi ← getConstInfo original
  let ci ← getConstInfo certificate
  unless oi.levelParams.length == ci.levelParams.length do
    throwError "Universe-parameter mismatch"
  let levels := oi.levelParams.map Level.param
  let originalType ← inferType (mkConst original levels)
  unless ← isDefEq originalType (← inferType (mkConst certificate levels)) do
    throwError "The full certificate changes the original target type"
  logInfo m!"EXACT TYPE: {original} = {certificate}"
  if ← isDefEq originalType (mkConst ``False) then
    throwError "Changed proposition accepted"
  logInfo "NEGATIVE CONTROL: changed proposition rejected"

#print axioms Kazemi.Hypercube.full_conjecture6_1
#print axioms Kazemi.Certificate.even_dimension_domination
#print axioms Kazemi.Certificate.coloring_lower_bound
#print axioms Kazemi.Certificate.code_coloring
#print axioms Kazemi.Hypercube.conjecture6_1
