import Proofs.WOWII376354.WOWII354Full
import Proofs.WOWII376354.WOWII376Full
import Lean.Util.CollectAxioms

/-! Exact imported endpoint types and transitive axiom audits with an admitted negative control. -/

open Lean Meta Elab Command in
run_elab do
  let pairs : Array (Name × Name) := #[
    (`WrittenOnTheWallII.GraphConjecture354.closed_neighborhood_bound,
      `WrittenOnTheWallII.GraphConjecture354.full_closed_neighborhood_bound),
    (`WrittenOnTheWallII.GraphConjecture354.degree_two_bound,
      `WrittenOnTheWallII.GraphConjecture354.full_degree_two_bound),
    (`WrittenOnTheWallII.GraphConjecture354.conjecture354_closed,
      `WrittenOnTheWallII.GraphConjecture354.full_conjecture354_closed),
    (`WrittenOnTheWallII.GraphConjecture376.conjecture376,
      `WrittenOnTheWallII.GraphConjecture376.full_conjecture376)]
  for (original, certificate) in pairs do
    let a ← mkConstWithFreshMVarLevels original
    let b ← mkConstWithFreshMVarLevels certificate
    let ta ← inferType a
    let tb ← inferType b
    unless ← isDefEq ta tb do
      throwError "Target mismatch: {original} and {certificate}"
    logInfo m!"EXACT TYPE: {original} = {certificate}"

#print axioms WrittenOnTheWallII.GraphConjecture354.full_closed_neighborhood_bound
#print axioms WrittenOnTheWallII.GraphConjecture354.full_degree_two_bound
#print axioms WrittenOnTheWallII.GraphConjecture354.full_conjecture354_closed
#print axioms WrittenOnTheWallII.GraphConjecture376.full_conjecture376
#print axioms WrittenOnTheWallII.GraphConjecture376.conjecture376
