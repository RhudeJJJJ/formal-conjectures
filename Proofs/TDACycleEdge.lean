import Proofs.TDAGraphBasics
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-! A connected non-tree with a high-degree vertex has a high-degree cycle endpoint. -/

namespace TotalDominationAnnihilationProof
open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
theorem cycle_neighbors (G : SimpleGraph V) {r : V} (P : G.Walk r r)
    (hP : P.IsCycle) {v : V} (hv : v ∈ P.support) :
    ∃ a b : V, a ≠ b ∧ G.Adj v a ∧ G.Adj v b ∧
      a ∈ P.support ∧ b ∈ P.support ∧ ¬ G.IsBridge s(v, a) := by
  classical
  let Q := P.rotate v hv
  have hQ : Q.IsCycle := hP.rotate hv
  have hQa : Q.snd ∈ P.support := by
    have h := Q.getVert_mem_support 1
    simpa only [Q, SimpleGraph.Walk.mem_support_rotate_iff] using h
  have hQb : Q.penultimate ∈ P.support := by
    have h := Q.getVert_mem_support (Q.length - 1)
    simpa only [Q, SimpleGraph.Walk.mem_support_rotate_iff] using h
  have hfirst : s(v, Q.snd) ∈ Q.edges := by
    apply Q.mk_mem_edges_iff_exists.mpr
    refine ⟨0, by have h := hQ.three_le_length; omega, ?_⟩
    simp
  refine ⟨Q.snd, Q.penultimate, hQ.snd_ne_penultimate,
    Q.adj_snd hQ.not_nil, (Q.adj_penultimate hQ.not_nil).symm, hQa, hQb, ?_⟩
  intro hbridge
  exact hbridge.notMem_edges_of_isCycle hQ hfirst

/-- If every vertex of a cycle has degree at most two, its support is closed. -/
theorem cycle_support_closed_of_degree_le_two (G : SimpleGraph V) [DecidableRel G.Adj]
    {r : V} (P : G.Walk r r) (hP : P.IsCycle)
    (hlow : ∀ v ∈ P.support, G.degree v ≤ 2) :
    ∀ v ∈ P.support, ∀ w, G.Adj v w → w ∈ P.support := by
  classical
  intro v hv w hvw
  obtain ⟨a, b, hab, hva, hvb, haP, hbP, _⟩ := cycle_neighbors G P hP hv
  have hsub : ({a, b} : Finset V) ⊆ G.neighborFinset v := by
    intro z hz
    rcases (by simpa only [mem_insert, mem_singleton] using hz : z = a ∨ z = b) with rfl | rfl
    · exact (mem_neighborFinset _ _ _).mpr hva
    · exact (mem_neighborFinset _ _ _).mpr hvb
  have hcard : (G.neighborFinset v).card ≤ ({a, b} : Finset V).card := by
    have h := hlow v hv
    simpa [hab] using h
  have heq : ({a, b} : Finset V) = G.neighborFinset v := eq_of_subset_of_card_le hsub hcard
  have hw : w ∈ ({a, b} : Finset V) := by
    rw [heq]
    exact (mem_neighborFinset _ _ _).mpr hvw
  rcases (by simpa only [mem_insert, mem_singleton] using hw : w = a ∨ w = b) with rfl | rfl
  · exact haP
  · exact hbP

theorem exists_nonbridge_high_endpoint (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Connected) (hntree : ¬ G.IsTree) (hhigh : ∃ v, 3 ≤ G.degree v) :
    ∃ u v : V, G.Adj u v ∧ 3 ≤ G.degree v ∧ ¬ G.IsBridge s(u, v) := by
  classical
  have hnot : ¬ G.IsAcyclic := fun h => hntree ⟨hG, h⟩
  have hcycle : ∃ r : V, ∃ P : G.Walk r r, P.IsCycle := by
    simpa only [SimpleGraph.IsAcyclic, not_forall, not_not] using hnot
  obtain ⟨r, P, hP⟩ := hcycle
  have hex : ∃ v ∈ P.support, 3 ≤ G.degree v := by
    by_contra hbad
    have hlow : ∀ v ∈ P.support, G.degree v ≤ 2 := by
      intro v hv
      by_contra hdeg
      exact hbad ⟨v, hv, by omega⟩
    let S := P.support.toFinset
    have hclosed : ∀ v ∈ S, ∀ w, G.Adj v w → w ∈ S := by
      intro v hv w hvw
      exact List.mem_toFinset.mpr
        (cycle_support_closed_of_degree_le_two G P hP hlow v (List.mem_toFinset.mp hv) w hvw)
    have hS := closed_set_eq_univ G hG.preconnected S
      ⟨r, List.mem_toFinset.mpr P.start_mem_support⟩ hclosed
    obtain ⟨v, hvhigh⟩ := hhigh
    have hvS : v ∈ S := by rw [hS]; exact mem_univ _
    have hvP := List.mem_toFinset.mp hvS
    have hvlow := hlow v hvP
    omega
  obtain ⟨v, hvP, hvhigh⟩ := hex
  obtain ⟨u, _, _, hvu, _, _, _, hnonbridge⟩ := cycle_neighbors G P hP hvP
  refine ⟨u, v, hvu.symm, hvhigh, ?_⟩
  intro hbridge
  apply hnonbridge
  have heq : s(u, v) = s(v, u) := Sym2.eq_swap
  exact heq ▸ hbridge

end TotalDominationAnnihilationProof

#print axioms TotalDominationAnnihilationProof.exists_nonbridge_high_endpoint
