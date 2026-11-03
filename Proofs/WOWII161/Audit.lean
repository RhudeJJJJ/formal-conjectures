import Proofs.WOWII161.Proof
import FormalConjectures.WrittenOnTheWallII.GraphConjecture161

open Lean Meta Elab Command in
run_elab do
  let target ← getConstInfo ``WrittenOnTheWallII.GraphConjecture161.conjecture161
  let proof ← getConstInfo ``WrittenOnTheWallII.GraphConjecture161.conjecture161_proved
  let targetType := target.type.instantiateLevelParams target.levelParams
    (proof.levelParams.map Level.param)
  unless ← isDefEq targetType proof.type do
    throwError "Certificate type differs from the original statement"
  logInfo "EXACT TYPE: certificate matches conjecture161, including all hypotheses"

#print axioms WrittenOnTheWallII.GraphConjecture161.conjecture161_proved
#print axioms WOWII161.tree_degree_le_leaves
#print axioms WOWII161.degree_le_Ls
#print axioms WOWII161.proper_clique_card_le_Ls
#print axioms WrittenOnTheWallII.GraphConjecture161.conjecture161
