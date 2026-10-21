import Proofs.TreeBounds
import Proofs.Potential348
import Lean.Util.CollectAxioms

/-! The exact quantified PR targets, proved without invoking their placeholders. -/
namespace WOWIIExactTargets
open SimpleGraph

theorem conjecture348_complete :
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      [DecidableRel G.Adj], G.IsTree → 2 < Fintype.card V →
        2 * (WrittenOnTheWallII.GraphConjecture348.externalDegreeTwoNeighbors G).card ≤
          3 * G.totalDominationNumber := by
  intro V _ _ G _ hT hn
  exact WOWIIRootedFlow.positive_348 G hT hn

theorem unique_mode_complete :
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      [DecidableRel G.Adj], G.IsTree → 2 < Fintype.card V →
        WrittenOnTheWallII.GraphConjecture367.TwoIsUniqueMode G →
          4 * WrittenOnTheWallII.GraphConjecture367.distinctDegreeCount G ≤
            3 * G.totalDominationNumber := by
  intro V _ _ G _ hT hn hm
  exact WOWIITreeProof.positive_367 G hT hn hm
end WOWIIExactTargets

#print axioms WOWIIExactTargets.conjecture348_complete
#print axioms WOWIIExactTargets.unique_mode_complete
run_cmd do
  let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for target in #[``WOWIIExactTargets.conjecture348_complete,
      ``WOWIIExactTargets.unique_mode_complete] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless allowed.contains ax do
        Lean.throwError m!"Unexpected axiom in {target}: {ax}"
    Lean.logInfo m!"Checked exact PR target {target}: {axioms}"
  let negative ← Lean.collectAxioms ``sorryAx
  unless negative.contains ``sorryAx && !(negative.all allowed.contains) do
    Lean.throwError "Placeholder negative control was not rejected"
  Lean.logInfo "WOWII_EXACT_TARGETS_PASS"
