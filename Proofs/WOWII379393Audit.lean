import Proofs.WOWII393aProof
import Proofs.WOWII379Proof
import Lean.Util.CollectAxioms

/-! Exact submitted target types and strict transitive axiom checks. -/
open SimpleGraph Finset
namespace WrittenOnTheWallII.GraphConjecture393
example {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : G.Connected) (horder : 2 < Fintype.card V) :
    (twoDominationNumber G : ℝ) ≤ (remainder G).card +
      matchingNumberOn G (neighbors G (supports G)) + (pendants G).card :=
  WOWII393aProof.conjecture393a G hG horder
end WrittenOnTheWallII.GraphConjecture393

namespace WrittenOnTheWallII.GraphConjecture379
example {V : Type*} [Fintype V] [DecidableEq V] (T : SimpleGraph V)
    [DecidableRel T.Adj] (hT : T.IsTree) (horder : 1 < Fintype.card V) :
    (componentsOn T (maximumVertices T) : ℚ) + (degreeDiversity T : ℚ) / 3 ≤
      T.totalDominationNumber := WOWII379Proof.conjecture379 T hT horder

example {V : Type*} [Fintype V] [DecidableEq V] (T : SimpleGraph V)
    [DecidableRel T.Adj] (hT : T.IsTree) (horder : 2 < Fintype.card V) (D : Finset V)
    (hD : T.IsTotalDominating (D : Set V)) :
    (componentsOn T (maximumVertices T) : ℚ) + max 1 (((degreeDiversity T : ℚ)-1)/2) ≤
      (D.card : ℚ) := WOWII379Proof.conjecture379_strengthened T hT horder D hD
end WrittenOnTheWallII.GraphConjecture379

run_cmd do
  let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for target in #[``FiniteMatchingCover.no_augment_three,
      ``FiniteMatchingCover.dominating_selection,
      ``FiniteMatchingCover.card_le_matchingNumber_on,
      ``ForestCounting.forest_card, ``ForestCounting.components_le_innerEdges,
      ``TotalDominationForestBudget.exact_budget,
      ``TotalDominationForestBudget.outside_degree,
      ``TotalDominationForestBudget.maximum_outside_budget,
      ``WOWII393aProof.conjecture393a, ``WOWII379Proof.degree_counts,
      ``WOWII379Proof.conjecture379_strengthened, ``WOWII379Proof.conjecture379] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless allowed.contains ax do
        Lean.throwError m!"Unexpected axiom in {target}: {ax}"
    Lean.logInfo m!"EXACT_CERTIFICATE_PASS {target}: {axioms}"
  let negative ← Lean.collectAxioms ``sorryAx
  unless negative.contains ``sorryAx && !(negative.all allowed.contains) do
    Lean.throwError "Placeholder negative control must fail the whitelist"
  Lean.logInfo "PLACEHOLDER_NEGATIVE_CONTROL_PASS"
