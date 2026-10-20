import Proofs.WOWII412eBounds
import Proofs.WOWII412abBounds
import FormalConjectures.WrittenOnTheWallII.GraphConjecture412e
import FormalConjectures.WrittenOnTheWallII.GraphConjecture412ab

/-!
# Exact certificates for WOWII 412a, 412b and 412e

The submitted definitions are identified with the proved internal invariants.
Source: Gebendorfer's two manuscripts dated 1 September 2026. OpenAI Codex
assisted with the cardinality reservation argument, formalization and checks.
-/
namespace WOWII412FamilyProof
open Finset SimpleGraph WrittenOnTheWallII
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

lemma critical_union_e (hb : G.IsBipartite) : GraphConjecture412e.criticalUnion G = WOWII412dCore.corona G := by
  classical
  have he : GraphConjecture412e.criticalUnion G = WOWII412dCore.criticalUnion G := by
    ext v
    simp only [GraphConjecture412e.criticalUnion, WOWII412dCore.criticalUnion, mem_filter, mem_univ, true_and]
    simp only [GraphConjecture412e.IsMaximumCriticalIndependent, WOWII412dCore.MaximumCritical,
      GraphConjecture412e.IsCriticalIndependent, WOWII412dCore.Critical, WOWII412dCore.independent_iff,
      GraphConjecture412e.difference, WOWII412dCore.difference, GraphConjecture412e.neighbors, WOWII412dCore.neighbors]
  rw [he, WOWII412dCore.criticalUnion_eq_corona_of_bipartite G hb]

lemma critical_union_ab (hb : G.IsBipartite) : GraphConjecture412ab.criticalUnion G = WOWII412dCore.corona G := by
  classical
  have he : GraphConjecture412ab.criticalUnion G = WOWII412dCore.criticalUnion G := by
    ext v
    simp only [GraphConjecture412ab.criticalUnion, WOWII412dCore.criticalUnion, mem_filter, mem_univ, true_and]
    simp only [GraphConjecture412ab.IsMaximumCriticalIndependent, WOWII412dCore.MaximumCritical,
      GraphConjecture412ab.IsCriticalIndependent, WOWII412dCore.Critical, WOWII412dCore.independent_iff,
      GraphConjecture412ab.difference, WOWII412dCore.difference, GraphConjecture412ab.neighbors, WOWII412dCore.neighbors]
  rw [he, WOWII412dCore.criticalUnion_eq_corona_of_bipartite G hb]

lemma corona_ab : GraphConjecture412ab.corona G = WOWII412dCore.corona G := by
  classical
  ext v
  simp only [GraphConjecture412ab.corona, WOWII412dCore.corona, mem_filter, mem_univ, true_and]
  simp only [GraphConjecture412ab.IsMaximumIndependent, WOWII412dCore.Maximum, WOWII412dCore.independent_iff]

omit [DecidableEq V] in
lemma pendants_e [DecidableRel G.Adj] : GraphConjecture412e.pendants G = PendantSupport.leaves G := by
  classical
  ext v
  simp only [GraphConjecture412e.pendants, PendantSupport.leaves, mem_filter, mem_univ, true_and,
    PendantSupport.degree_nat_card]

omit [DecidableEq V] in
lemma pendants_ab [DecidableRel G.Adj] : GraphConjecture412ab.pendants G = PendantSupport.leaves G := by
  classical
  ext v
  simp only [GraphConjecture412ab.pendants, PendantSupport.leaves, mem_filter, mem_univ, true_and,
    PendantSupport.degree_nat_card]

omit [DecidableEq V] in
lemma degreeTwo_ab [DecidableRel G.Adj] : GraphConjecture412ab.degreeTwo G = WOWII412abBounds.degreeTwo G := by
  classical
  ext v
  simp only [GraphConjecture412ab.degreeTwo, WOWII412abBounds.degreeTwo, mem_filter, mem_univ, true_and,
    PendantSupport.degree_nat_card]

/-- The exact literal-neighborhood WOWII 412e statement. -/
theorem conjecture412e [DecidableRel G.Adj] (_hG : G.Connected)
    (hb : G.IsBipartite) (horder : 2 < Fintype.card V) :
    1 + GraphConjecture412e.inducedMaxDegree G (GraphConjecture412e.neighbors G (GraphConjecture412e.neighbors G (GraphConjecture412e.pendants G))) ≤
      (GraphConjecture412e.criticalUnion G).card := by
  rw [critical_union_e G hb, pendants_e G]
  exact WOWII412eBounds.literal_bound G hb horder

/-- The exact external-neighborhood strengthening of WOWII 412e. -/
theorem conjecture412e_external [DecidableRel G.Adj] (hG : G.Connected)
    (hb : G.IsBipartite) (horder : 2 < Fintype.card V) :
    GraphConjecture412e.inducedMaxDegree G (GraphConjecture412e.externalNeighbors G (GraphConjecture412e.externalNeighbors G (GraphConjecture412e.pendants G))) +
      max 2 (GraphConjecture412e.pendants G).card ≤ G.indepNum ∧ G.indepNum ≤ (GraphConjecture412e.criticalUnion G).card := by
  classical
  have hfirst : GraphConjecture412e.externalNeighbors G (GraphConjecture412e.pendants G) = PendantSupport.supports G := by
    rw [pendants_e G]
    change WOWII412dCore.neighbors G (PendantSupport.leaves G) \ PendantSupport.leaves G = _
    exact sdiff_eq_left.mpr
      (WOWII412dCore.independent_disjoint_neighbors G _ (PendantSupport.leaves_independent G hG horder)).symm
  constructor
  · rw [hfirst, pendants_e G]
    exact WOWII412eBounds.external_bound G hG hb horder
  · rw [critical_union_e G hb]
    exact PendantSupport.indepNum_le_corona G

/-- The exact general corona strengthening of WOWII 412a. -/
theorem conjecture412a_corona [DecidableRel G.Adj] (_hG : G.Connected)
    (_horder : 2 < Fintype.card V) :
    GraphConjecture412ab.largestComponentOrder G (GraphConjecture412ab.neighbors G (GraphConjecture412ab.pendants G)) +
      GraphConjecture412ab.independentOn G (univ \ GraphConjecture412ab.neighbors G (GraphConjecture412ab.neighbors G (GraphConjecture412ab.pendants G))) ≤
        (GraphConjecture412ab.corona G).card := by
  rw [pendants_ab G, corona_ab G]
  exact WOWII412abBounds.residual_bound G

/-- The exact general corona strengthening of WOWII 412b. -/
theorem conjecture412b_corona [DecidableRel G.Adj] (hG : G.Connected)
    (horder : 2 < Fintype.card V) :
    GraphConjecture412ab.largestComponentOrder G (GraphConjecture412ab.neighbors G (GraphConjecture412ab.pendants G)) +
      GraphConjecture412ab.independentOn G (GraphConjecture412ab.degreeTwo G) ≤ (GraphConjecture412ab.corona G).card := by
  rw [pendants_ab G, degreeTwo_ab G, corona_ab G]
  exact WOWII412abBounds.degree_two_bound G hG horder

/-- The exact original bipartite WOWII 412a statement. -/
theorem conjecture412a [DecidableRel G.Adj] (hG : G.Connected)
    (hb : G.IsBipartite) (horder : 2 < Fintype.card V) :
    GraphConjecture412ab.largestComponentOrder G (GraphConjecture412ab.neighbors G (GraphConjecture412ab.pendants G)) +
      GraphConjecture412ab.independentOn G (univ \ GraphConjecture412ab.neighbors G (GraphConjecture412ab.neighbors G (GraphConjecture412ab.pendants G))) ≤
        (GraphConjecture412ab.criticalUnion G).card := by
  rw [critical_union_ab G hb, ← corona_ab G]
  exact conjecture412a_corona G hG horder

/-- The exact original bipartite WOWII 412b statement. -/
theorem conjecture412b [DecidableRel G.Adj] (hG : G.Connected)
    (hb : G.IsBipartite) (horder : 2 < Fintype.card V) :
    GraphConjecture412ab.largestComponentOrder G (GraphConjecture412ab.neighbors G (GraphConjecture412ab.pendants G)) +
      GraphConjecture412ab.independentOn G (GraphConjecture412ab.degreeTwo G) ≤ (GraphConjecture412ab.criticalUnion G).card := by
  rw [critical_union_ab G hb, ← corona_ab G]
  exact conjecture412b_corona G hG horder

end WOWII412FamilyProof
