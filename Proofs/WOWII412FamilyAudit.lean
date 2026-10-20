import Proofs.WOWII412FamilyProof
import Lean.Util.CollectAxioms

/-! Exact submitted target types and strict transitive-axiom guards. -/
open SimpleGraph Finset
namespace WrittenOnTheWallII.GraphConjecture412e
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

example [DecidableRel G.Adj] (hG : G.Connected) (hb : G.IsBipartite)
    (horder : 2 < Fintype.card V) :
    1 + inducedMaxDegree G (neighbors G (neighbors G (pendants G))) ≤
      (criticalUnion G).card :=
  WOWII412FamilyProof.conjecture412e G hG hb horder

example [DecidableRel G.Adj] (hG : G.Connected) (hb : G.IsBipartite)
    (horder : 2 < Fintype.card V) :
    inducedMaxDegree G (externalNeighbors G (externalNeighbors G (pendants G))) +
      max 2 (pendants G).card ≤ G.indepNum ∧ G.indepNum ≤ (criticalUnion G).card :=
  WOWII412FamilyProof.conjecture412e_external G hG hb horder
end WrittenOnTheWallII.GraphConjecture412e

namespace WrittenOnTheWallII.GraphConjecture412ab
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

example [DecidableRel G.Adj] (hG : G.Connected) (hb : G.IsBipartite)
    (horder : 2 < Fintype.card V) :
    largestComponentOrder G (neighbors G (pendants G)) +
      independentOn G (univ \ neighbors G (neighbors G (pendants G))) ≤
        (criticalUnion G).card :=
  WOWII412FamilyProof.conjecture412a G hG hb horder

example [DecidableRel G.Adj] (hG : G.Connected) (hb : G.IsBipartite)
    (horder : 2 < Fintype.card V) :
    largestComponentOrder G (neighbors G (pendants G)) + independentOn G (degreeTwo G) ≤
      (criticalUnion G).card :=
  WOWII412FamilyProof.conjecture412b G hG hb horder

example [DecidableRel G.Adj] (hG : G.Connected) (horder : 2 < Fintype.card V) :
    largestComponentOrder G (neighbors G (pendants G)) +
      independentOn G (univ \ neighbors G (neighbors G (pendants G))) ≤ (corona G).card :=
  WOWII412FamilyProof.conjecture412a_corona G hG horder

example [DecidableRel G.Adj] (hG : G.Connected) (horder : 2 < Fintype.card V) :
    largestComponentOrder G (neighbors G (pendants G)) + independentOn G (degreeTwo G) ≤
      (corona G).card :=
  WOWII412FamilyProof.conjecture412b_corona G hG horder
end WrittenOnTheWallII.GraphConjecture412ab

run_cmd do
  let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for target in #[``CoronaExchange.strict_neighbors, ``CoronaExchange.reserved_cardinality,
      ``SupportComponentBounds.reserve_largest_component,
      ``WOWII412abBounds.degree_two_support_mem_corona,
      ``WOWII412FamilyProof.conjecture412e, ``WOWII412FamilyProof.conjecture412e_external,
      ``WOWII412FamilyProof.conjecture412a, ``WOWII412FamilyProof.conjecture412b,
      ``WOWII412FamilyProof.conjecture412a_corona, ``WOWII412FamilyProof.conjecture412b_corona] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless allowed.contains ax do
        Lean.throwError m!"Unexpected axiom in {target}: {ax}"
    Lean.logInfo m!"EXACT_CERTIFICATE_PASS {target}: {axioms}"
  let negative ← Lean.collectAxioms ``sorryAx
  unless negative.contains ``sorryAx && !(negative.all allowed.contains) do
    Lean.throwError "Placeholder negative control must fail the whitelist"
  Lean.logInfo "PLACEHOLDER_NEGATIVE_CONTROL_PASS"
