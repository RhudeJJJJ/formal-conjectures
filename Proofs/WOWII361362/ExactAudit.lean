import Proofs.WOWII361362.WOWII362Full
import Proofs.WOWII361362.WOWII361Full
import Lean.Util.CollectAxioms

/-! Exact type and transitive-axiom audits, including an admitted negative control. -/

open Lean Meta Elab Command in
run_elab do
  let pairs : Array (Name × Name) := #[
    (`WrittenOnTheWallII.GraphConjecture362.conjecture362,
      `WrittenOnTheWallII.GraphConjecture362.full_conjecture362),
    (`WrittenOnTheWallII.GraphConjecture362.conjecture362_diameter,
      `WrittenOnTheWallII.GraphConjecture362.full_conjecture362_diameter),
    (`WrittenOnTheWallII.GraphConjecture361.conjecture361,
      `WrittenOnTheWallII.GraphConjecture361.full_conjecture361),
    (`WrittenOnTheWallII.GraphConjecture361.conjecture361_nontrivial,
      `WrittenOnTheWallII.GraphConjecture361.full_conjecture361_nontrivial)]
  for (original, certificate) in pairs do
    let a ← mkConstWithFreshMVarLevels original
    let b ← mkConstWithFreshMVarLevels certificate
    let ta ← inferType a
    let tb ← inferType b
    unless ← isDefEq ta tb do
      throwError "Target mismatch: {original} and {certificate}"
    logInfo m!"EXACT TYPE: {original} = {certificate}"

#print axioms WrittenOnTheWallII.GraphConjecture362.full_conjecture362
#print axioms WrittenOnTheWallII.GraphConjecture362.full_conjecture362_diameter
#print axioms WrittenOnTheWallII.GraphConjecture361.full_conjecture361
#print axioms WrittenOnTheWallII.GraphConjecture361.full_conjecture361_nontrivial

-- The admitted source target is only a negative control.
#print axioms WrittenOnTheWallII.GraphConjecture361.conjecture361
