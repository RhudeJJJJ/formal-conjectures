import Proofs.CoronaTwoDominatingProof
import Proofs.WOWII412dCore
import Mathlib.Combinatorics.SimpleGraph.Bipartite

/-!
# WOWII 405 and 407

The critical union equals the corona in bipartite graphs, by the mixed-set
argument in the reused WOWII412dCore checkpoint. The corona exchange theorem
then makes its private external-neighbor count zero. The two tree bounds
follow because their right sides are natural numbers.

Written source: Gebendorfer, The Corona of a Graph Is 2-Dominating,
31 August 2026, revision R2, linked in issue 7267. The critical-set bridge is
established literature, as credited in that manuscript and the existing PR.
OpenAI Codex assisted with this composition and validation.
-/

namespace WOWII405407Proof
open SimpleGraph Finset WrittenOnTheWallII.GraphConjecture404To407

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

lemma exists_bipartition (h : G.IsBipartite) :
    ∃ A : Finset V, WOWII412dCore.Bipartition G A := by
  classical
  obtain ⟨c, hc⟩ := h
  refine ⟨univ.filter (fun v => c v = 0), ?_, ?_⟩
  · intro u hu v hv huv
    have hcu : c u = 0 := (mem_filter.mp hu).2
    have hcv : c v = 0 := (mem_filter.mp hv).2
    exact hc huv (hcu.trans hcv.symm)
  · intro u hu v hv huv
    have hcu : c u ≠ 0 := by simpa using (mem_sdiff.mp hu).2
    have hcv : c v ≠ 0 := by simpa using (mem_sdiff.mp hv).2
    have he : c u = c v := by omega
    exact hc huv he

lemma critical_union_eq_corona (hb : G.IsBipartite) :
    criticalUnion G = corona G := by
  classical
  obtain ⟨A, hA⟩ := exists_bipartition G hb
  have hcrit : criticalUnion G = WOWII412dCore.criticalUnion G := by
    ext v
    simp only [criticalUnion, WOWII412dCore.criticalUnion, mem_filter, mem_univ, true_and]
    simp only [IsMaximumCriticalIndependent, WOWII412dCore.MaximumCritical,
      IsCriticalIndependent, WOWII412dCore.Critical,
      WOWII412dCore.independent_iff, difference, WOWII412dCore.difference,
      neighbors, WOWII412dCore.neighbors]
  have hcorona : corona G = WOWII412dCore.corona G := by
    ext v
    simp only [corona, WOWII412dCore.corona, mem_filter, mem_univ, true_and]
    simp only [IsMaximumIndependent, WOWII412dCore.Maximum, WOWII412dCore.independent_iff]
  rw [hcrit, WOWII412dCore.criticalUnion_eq_corona G A hA, ← hcorona]

theorem private_external_neighbors_eq_zero [DecidableRel G.Adj]
    (hb : G.IsBipartite) :
    privateExternalNeighborCount G (criticalUnion G) = 0 := by
  classical
  rw [critical_union_eq_corona G hb]
  unfold privateExternalNeighborCount
  apply card_eq_zero.mpr
  apply filter_eq_empty_iff.mpr
  intro v _ hv
  have htwo := CoronaTwoDominatingProof.corona_two_dominating G v hv.1
  rw [hv.2] at htwo
  omega

theorem conjecture405 [DecidableRel G.Adj] (hT : G.IsTree)
    (_horder : 2 < Fintype.card V) :
    privateExternalNeighborCount G (criticalUnion G) ≤
      2 * (G.induce ((univ \ leaves G : Finset V) : Set V)).indepNum := by
  rw [private_external_neighbors_eq_zero G hT.isBipartite]
  exact Nat.zero_le _

theorem conjecture407 [DecidableRel G.Adj] (hT : G.IsTree)
    (_horder : 2 < Fintype.card V) :
    privateExternalNeighborCount G (criticalUnion G) ≤ 2 * G.pathCoverNumber := by
  rw [private_external_neighbors_eq_zero G hT.isBipartite]
  exact Nat.zero_le _

end WOWII405407Proof

#print axioms WOWII405407Proof.critical_union_eq_corona
#print axioms WOWII405407Proof.private_external_neighbors_eq_zero
#print axioms WOWII405407Proof.conjecture405
#print axioms WOWII405407Proof.conjecture407
