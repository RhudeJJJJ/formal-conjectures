/-
Copyright 2026 Jonas J. Gebendorfer.
Licensed under the Apache License, Version 2.0.
-/
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Domination
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.VertexDistance
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Independence
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Residue
import Mathlib.Tactic

/-! The explicit upper/M and upper/center readings of WOWII 430c.
The primary row has a missing comparison sign and a C/M mismatch.
Source: Gebendorfer, 7 September 2026, issue 7273.
OpenAI Codex assisted with formalization. -/
namespace WOWII430Proof
open SimpleGraph Finset
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def adjacency : Fin 105 → Finset (Fin 105) := ![{1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,41,42,43,44,49,50,51,52,89,90,91,92,101,102,103,104},{0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,45,46,47,48,53,54,55,56,93,94,95,96},{0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,25,26,27,28,29,30,31,32,49,50,51,52,57,58,59,60,97,98,99,100},{0,1,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,29,30,31,32,33,34,35,36,53,54,55,56,61,62,63,64,101,102,103,104},{0,1,2,3,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,33,34,35,36,37,38,39,40,57,58,59,60,65,66,67,68},{0,1,2,3,4,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,25,26,27,28,37,38,39,40,41,42,43,44,61,62,63,64,69,70,71,72},{0,1,2,3,4,5,7,8,9,10,11,12,13,14,15,16,17,18,19,20,29,30,31,32,41,42,43,44,45,46,47,48,65,66,67,68,73,74,75,76},{0,1,2,3,4,5,6,8,9,10,11,12,13,14,15,16,17,18,19,20,33,34,35,36,45,46,47,48,49,50,51,52,69,70,71,72,77,78,79,80},{0,1,2,3,4,5,6,7,9,10,11,12,13,14,15,16,17,18,19,20,37,38,39,40,49,50,51,52,53,54,55,56,73,74,75,76,81,82,83,84},{0,1,2,3,4,5,6,7,8,10,11,12,13,14,15,16,17,18,19,20,41,42,43,44,53,54,55,56,57,58,59,60,77,78,79,80,85,86,87,88},{0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16,17,18,19,20,45,46,47,48,57,58,59,60,61,62,63,64,81,82,83,84,89,90,91,92},{0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,17,18,19,20,49,50,51,52,61,62,63,64,65,66,67,68,85,86,87,88,93,94,95,96},{0,1,2,3,4,5,6,7,8,9,10,11,13,14,15,16,17,18,19,20,53,54,55,56,65,66,67,68,69,70,71,72,89,90,91,92,97,98,99,100},{0,1,2,3,4,5,6,7,8,9,10,11,12,14,15,16,17,18,19,20,57,58,59,60,69,70,71,72,73,74,75,76,93,94,95,96,101,102,103,104},{0,1,2,3,4,5,6,7,8,9,10,11,12,13,15,16,17,18,19,20,21,22,23,24,61,62,63,64,73,74,75,76,77,78,79,80,97,98,99,100},{0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,16,17,18,19,20,25,26,27,28,65,66,67,68,77,78,79,80,81,82,83,84,101,102,103,104},{0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,17,18,19,20,21,22,23,24,29,30,31,32,69,70,71,72,81,82,83,84,85,86,87,88},{0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,18,19,20,25,26,27,28,33,34,35,36,73,74,75,76,85,86,87,88,89,90,91,92},{0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,19,20,29,30,31,32,37,38,39,40,77,78,79,80,89,90,91,92,93,94,95,96},{0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,20,33,34,35,36,41,42,43,44,81,82,83,84,93,94,95,96,97,98,99,100},{0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,37,38,39,40,45,46,47,48,85,86,87,88,97,98,99,100,101,102,103,104},{0,1,4,14,16},{0,1,4,14,16},{0,1,4,14,16},{0,1,4,14,16},{1,2,5,15,17},{1,2,5,15,17},{1,2,5,15,17},{1,2,5,15,17},{2,3,6,16,18},{2,3,6,16,18},{2,3,6,16,18},{2,3,6,16,18},{3,4,7,17,19},{3,4,7,17,19},{3,4,7,17,19},{3,4,7,17,19},{4,5,8,18,20},{4,5,8,18,20},{4,5,8,18,20},{4,5,8,18,20},{0,5,6,9,19},{0,5,6,9,19},{0,5,6,9,19},{0,5,6,9,19},{1,6,7,10,20},{1,6,7,10,20},{1,6,7,10,20},{1,6,7,10,20},{0,2,7,8,11},{0,2,7,8,11},{0,2,7,8,11},{0,2,7,8,11},{1,3,8,9,12},{1,3,8,9,12},{1,3,8,9,12},{1,3,8,9,12},{2,4,9,10,13},{2,4,9,10,13},{2,4,9,10,13},{2,4,9,10,13},{3,5,10,11,14},{3,5,10,11,14},{3,5,10,11,14},{3,5,10,11,14},{4,6,11,12,15},{4,6,11,12,15},{4,6,11,12,15},{4,6,11,12,15},{5,7,12,13,16},{5,7,12,13,16},{5,7,12,13,16},{5,7,12,13,16},{6,8,13,14,17},{6,8,13,14,17},{6,8,13,14,17},{6,8,13,14,17},{7,9,14,15,18},{7,9,14,15,18},{7,9,14,15,18},{7,9,14,15,18},{8,10,15,16,19},{8,10,15,16,19},{8,10,15,16,19},{8,10,15,16,19},{9,11,16,17,20},{9,11,16,17,20},{9,11,16,17,20},{9,11,16,17,20},{0,10,12,17,18},{0,10,12,17,18},{0,10,12,17,18},{0,10,12,17,18},{1,11,13,18,19},{1,11,13,18,19},{1,11,13,18,19},{1,11,13,18,19},{2,12,14,19,20},{2,12,14,19,20},{2,12,14,19,20},{2,12,14,19,20},{0,3,13,15,20},{0,3,13,15,20},{0,3,13,15,20},{0,3,13,15,20}]

def witness : SimpleGraph (Fin 105) where
  Adj u v := v ∈ adjacency u
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩
instance : DecidableRel witness.Adj := inferInstanceAs
  (DecidableRel fun u v : Fin 105 => v ∈ adjacency u)


def lineType (v : Fin 105) : Fin 21 := ⟨(v.val - 21) / 4, by omega⟩
def point (v : Fin 105) : Fin 105 := ⟨(lineType v).val, by have := (lineType v).isLt; omega⟩
def common : Fin 21 → Fin 21 → Fin 105 := ![![0,1,16,4,4,0,1,0,1,4,14,4,16,14,14,16,16,0,1,14,0],![1,1,2,17,5,5,1,2,1,2,5,15,5,17,15,15,17,17,1,2,15],![16,2,2,3,18,6,6,2,3,2,3,6,16,6,18,16,16,18,18,2,3],![4,17,3,3,4,19,7,7,3,4,3,4,7,17,7,19,17,17,19,19,3],![4,5,18,4,4,5,20,8,8,4,5,4,5,8,18,8,20,18,18,20,20],![0,5,6,19,5,0,6,0,9,9,5,6,5,6,9,19,9,0,19,19,0],![1,1,6,7,20,6,1,7,1,10,10,6,7,6,7,10,20,10,1,20,20],![0,2,2,7,8,0,7,0,8,2,11,11,7,8,7,8,11,0,11,2,0],![1,1,3,3,8,9,1,8,1,9,3,12,12,8,9,8,9,12,1,12,3],![4,2,2,4,4,9,10,2,9,2,10,4,13,13,9,10,9,10,13,2,13],![14,5,3,3,5,5,10,11,3,10,3,11,5,14,14,10,11,10,11,14,3],![4,15,6,4,4,6,6,11,12,4,11,4,12,6,15,15,11,12,11,12,15],![16,5,16,7,5,5,7,7,12,13,5,12,5,13,7,16,16,12,13,12,13],![14,17,6,17,8,6,6,8,8,13,14,6,13,6,14,8,17,17,13,14,13],![14,15,18,7,18,9,7,7,9,9,14,15,7,14,7,15,9,18,18,14,15],![16,15,16,19,8,19,10,8,8,10,10,15,16,8,15,8,16,10,19,19,15],![16,17,16,17,20,9,20,11,9,9,11,11,16,17,9,16,9,17,11,20,20],![0,17,18,17,18,0,10,0,12,10,10,12,12,17,18,10,17,0,18,12,0],![1,1,18,19,18,19,1,11,1,13,11,11,13,13,18,19,11,18,1,19,13],![14,2,2,19,20,19,20,2,12,2,14,12,12,14,14,19,20,12,19,2,20],![0,15,3,3,20,0,20,0,3,13,3,15,13,13,15,15,20,0,13,20,0]]

def via (u v : Fin 105) : Fin 105 :=
  if u.val < 21 then point v else if v.val < 21 then point u else common (lineType u) (lineType v)
lemma two_step_certificate : ∀ u v : Fin 105, u ≠ v →
    witness.Adj u v ∨ (witness.Adj u (via u v) ∧ witness.Adj (via u v) v) := by decide
lemma short_walk (u v : Fin 105) : ∃ p : witness.Walk u v, p.length ≤ 2 := by
  by_cases he : u = v
  · subst v; exact ⟨.nil, by simp⟩
  · rcases two_step_certificate u v he with h | ⟨h₁,h₂⟩
    · exact ⟨.cons h .nil, by simp⟩
    · exact ⟨.cons h₁ (.cons h₂ .nil), by simp⟩
lemma witness_connected : witness.Connected :=
  ⟨fun u v => (short_walk u v).elim fun p _ => p.reachable⟩
lemma square_complete : witness.graphSquare = ⊤ := by
  ext u v
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h, ?_⟩
    obtain ⟨p, hp⟩ := short_walk u v
    exact p.edist_le.trans (by exact_mod_cast hp)


def degrees : Fin 105 → ℕ := ![40,40,40,40,40,40,40,40,40,40,40,40,40,40,40,40,40,40,40,40,40,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5]
lemma degree_eq : ∀ v : Fin 105, witness.degree v = degrees v := by decide
lemma degree_bound : ∀ v : Fin 105, degrees v ≤ 40 := by decide
lemma global_degree_bound : witness.maxDegree ≤ 40 :=
  witness.maxDegree_le_of_forall_degree_le 40 (fun v => by rw [degree_eq]; exact degree_bound v)

def clique : Finset (Fin 105) := univ.filter fun v => v.val < 21
def outer : Finset (Fin 105) := univ \ clique
def forced (c : Fin 105) : Finset (Fin 105) := insert c (outer \ adjacency c)
lemma clique_edges : ∀ c ∈ clique, ∀ w ∈ clique, c ≠ w → witness.Adj c w := by decide
lemma outer_adj : ∀ u ∈ outer, ∀ w : Fin 105, witness.Adj u w → w ∈ clique := by decide
lemma forced_card : ∀ c ∈ clique, 65 ≤ (forced c).card := by decide
lemma outer_card : outer.card = 84 := by decide

/-- A lower bound for EVERY independent dominating set, without powerset enumeration. -/
lemma independent_dominating_lower (D : Finset (Fin 105))
    (hD : witness.IsIndepDominating (D : Set (Fin 105))) : 65 ≤ D.card := by
  classical
  by_cases hc : (D ∩ clique).Nonempty
  · obtain ⟨c, hc⟩ := hc
    have hcd := (mem_inter.mp hc).1
    have hcc := (mem_inter.mp hc).2
    have hs : forced c ⊆ D := by
      intro u hu
      rcases mem_insert.mp hu with rfl | hu
      · exact hcd
      · rcases hD.2 u with hd | ⟨w, hw, huw⟩
        · exact hd
        · have hwc := outer_adj u (mem_sdiff.mp hu).1 w huw
          have he : w = c := by
            by_contra hn
            exact hD.1 hcd hw (Ne.symm hn) (clique_edges c hcc w hwc (Ne.symm hn))
          subst w
          exact False.elim ((mem_sdiff.mp hu).2 huw.symm)
    exact (forced_card c hcc).trans (card_le_card hs)
  · have hs : outer ⊆ D := by
      intro u hu
      rcases hD.2 u with hd | ⟨w, hw, huw⟩
      · exact hd
      · exact False.elim (hc ⟨w, mem_inter.mpr ⟨hw, outer_adj u hu w huw⟩⟩)
    have hh := card_le_card hs
    rw [outer_card] at hh
    omega

def selected : Finset (Fin 105) := forced 0
lemma selected_certificate : witness.IsIndepDominating (selected : Set (Fin 105)) ∧
    selected.card = 65 := by
  constructor
  · change (∀ u ∈ selected, ∀ v ∈ selected, u ≠ v → ¬ witness.Adj u v) ∧
      (∀ v, v ∈ selected ∨ ∃ w ∈ selected, witness.Adj v w)
    decide
  · decide
lemma independent_domination_eq : witness.indepDominationNumber = 65 := by
  apply le_antisymm
  · exact Nat.sInf_le ⟨selected, selected_certificate.1.1, selected_certificate.1.2,
      selected_certificate.2⟩
  · apply le_csInf
    · exact ⟨65, selected, selected_certificate.1.1, selected_certificate.1.2,
        selected_certificate.2⟩
    · rintro n ⟨D, hD⟩
      rw [← hD.card_eq]
      exact independent_dominating_lower D ⟨hD.isIndep, hD.isDominating⟩



end WOWII430Proof
