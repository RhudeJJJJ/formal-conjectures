import Proofs.WOWII412dCover
import FormalConjectures.WrittenOnTheWallII.GraphConjecture412d

/-!
# Complete Lean certificates for WOWII 412d

The isolate-free strengthened statement and the original connected statement
are derived from the proved core cover, using the exact submitted definitions.
Source: Jonas J. Gebendorfer, Total domination and the union of maximum critical
independent sets in bipartite graphs, 11 October 2026. OpenAI Codex assisted
with the new ranked-forest construction, composition and validation.
-/
namespace WOWII412dProof
open SimpleGraph Finset WrittenOnTheWallII.GraphConjecture412d
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

lemma criticalUnion_eq_internal : criticalUnion G = WOWII412dCore.criticalUnion G := by
  classical
  ext v
  simp only [criticalUnion, WOWII412dCore.criticalUnion, mem_filter, mem_univ, true_and]
  simp only [IsMaximumCriticalIndependent, WOWII412dCore.MaximumCritical,
    IsCriticalIndependent, WOWII412dCore.Critical,
    WOWII412dCore.independent_iff, difference, WOWII412dCore.difference,
    neighbors, WOWII412dCore.neighbors]

lemma corona_eq_internal : corona G = WOWII412dCore.corona G := by
  classical
  ext v
  simp only [corona, WOWII412dCore.corona, mem_filter, mem_univ, true_and]
  simp only [IsMaximumIndependent, WOWII412dCore.Maximum, WOWII412dCore.independent_iff]

/-- The exact strengthened target, including the identification of the two unions. -/
theorem conjecture412d_isolate_free (hb : G.IsBipartite)
    (hni : ∀ v, ∃ w, G.Adj v w) :
    G.totalDominationNumber ≤ (corona G).card ∧ corona G = criticalUnion G := by
  have he := WOWII412dCore.criticalUnion_eq_corona_of_bipartite G hb
  constructor
  · rw [corona_eq_internal G, ← he]
    exact WOWII412dCore.total_bound G hb hni
  · rw [corona_eq_internal G, criticalUnion_eq_internal G, he]

/-- The exact original connected formulation. -/
theorem conjecture412d (hG : G.Connected) (hb : G.IsBipartite)
    (horder : 2 < Fintype.card V) :
    G.totalDominationNumber ≤ (criticalUnion G).card := by
  have hni : ∀ v, ∃ w, G.Adj v w := connected_has_neighbor G hG horder
  have h := conjecture412d_isolate_free G hb hni
  exact h.2 ▸ h.1

end WOWII412dProof
