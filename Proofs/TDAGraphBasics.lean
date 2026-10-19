import Proofs.TDABudget
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-! Leaves, supports and the induced core, for the exact universal graph target. -/

namespace TotalDominationAnnihilationProof
open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

def leaves (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  univ.filter fun v => G.degree v = 1

def core (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V := univ \ leaves G

def coreNeighbors (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : Finset V :=
  G.neighborFinset v \ leaves G

def supports (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  univ.filter fun v => ∃ p ∈ leaves G, G.Adj v p

omit [DecidableEq V] in
@[simp] theorem mem_leaves {G : SimpleGraph V} [DecidableRel G.Adj] {v : V} :
    v ∈ leaves G ↔ G.degree v = 1 := by simp [leaves]

@[simp] theorem mem_core {G : SimpleGraph V} [DecidableRel G.Adj] {v : V} :
    v ∈ core G ↔ G.degree v ≠ 1 := by simp [core]

@[simp] theorem mem_coreNeighbors {G : SimpleGraph V} [DecidableRel G.Adj] {u v : V} :
    v ∈ coreNeighbors G u ↔ G.Adj u v ∧ v ∈ core G := by
  simp [coreNeighbors, mem_neighborFinset]

omit [DecidableEq V] in
@[simp] theorem mem_supports {G : SimpleGraph V} [DecidableRel G.Adj] {v : V} :
    v ∈ supports G ↔ ∃ p ∈ leaves G, G.Adj v p := by simp [supports]

theorem leaf_neighbor_unique (G : SimpleGraph V) [DecidableRel G.Adj]
    {p u v : V} (hp : p ∈ leaves G) (hpu : G.Adj p u) (hpv : G.Adj p v) : u = v := by
  have hcard : (G.neighborFinset p).card = 1 := mem_leaves.mp hp
  obtain ⟨w, hw⟩ := card_eq_one.mp hcard
  have hu : u = w := by simpa only [hw, mem_singleton] using (mem_neighborFinset _ _ _).mpr hpu
  have hv : v = w := by simpa only [hw, mem_singleton] using (mem_neighborFinset _ _ _).mpr hpv
  exact hu.trans hv.symm

/-- A nonempty adjacency-closed vertex set in a connected graph is the whole graph. -/
omit [DecidableEq V] in
theorem closed_set_eq_univ (G : SimpleGraph V) (hG : G.Preconnected) (S : Finset V)
    (hne : S.Nonempty) (hclosed : ∀ u ∈ S, ∀ v, G.Adj u v → v ∈ S) : S = univ := by
  obtain ⟨u, hu⟩ := hne
  apply eq_univ_of_forall
  intro v
  obtain ⟨p⟩ := hG u v
  have hwalk : ∀ {x y : V}, (q : G.Walk x y) → x ∈ S → y ∈ S := by
    intro x y q
    induction q with
    | nil => exact id
    | @cons x z y hxz q IH => exact fun hx => IH (hclosed x hx z hxz)
  exact hwalk p hu

theorem leaves_not_adjacent (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Preconnected) (hn : 3 ≤ Fintype.card V) {p q : V}
    (hp : p ∈ leaves G) (hq : q ∈ leaves G) : ¬ G.Adj p q := by
  intro hpq
  have hclosed : ∀ u ∈ ({p, q} : Finset V), ∀ v, G.Adj u v → v ∈ ({p, q} : Finset V) := by
    intro u hu v huv
    rcases (by simpa only [mem_insert, mem_singleton] using hu : u = p ∨ u = q) with rfl | rfl
    · have hvq := leaf_neighbor_unique G hp huv hpq
      simp [hvq]
    · have hvp := leaf_neighbor_unique G hq huv hpq.symm
      simp [hvp]
  have heq := closed_set_eq_univ G hG {p, q} (by simp) hclosed
  have hc : Fintype.card V ≤ 2 := by
    rw [← card_univ, ← heq]
    simp [hpq.ne]
  omega

theorem supports_subset_core (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Preconnected) (hn : 3 ≤ Fintype.card V) : supports G ⊆ core G := by
  intro v hv
  obtain ⟨p, hp, hvp⟩ := mem_supports.mp hv
  apply mem_core.mpr
  intro hvleaf
  exact leaves_not_adjacent G hG hn (mem_leaves.mpr hvleaf) hp hvp

theorem core_nonempty (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Connected) (hn : 3 ≤ Fintype.card V) : (core G).Nonempty := by
  let : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨p⟩ := hG.nonempty
  obtain ⟨q, hpq⟩ := (G.degree_pos_iff_exists_adj p).mp (hG.preconnected.degree_pos_of_nontrivial p)
  by_cases hp : p ∈ leaves G
  · refine ⟨q, mem_core.mpr ?_⟩
    intro hq
    exact leaves_not_adjacent G hG.preconnected hn hp (mem_leaves.mpr hq) hpq
  · exact ⟨p, mem_core.mpr (by simpa using hp)⟩

/-- With at least two core vertices, every core vertex has a core neighbor. -/
theorem core_neighbor_nonempty (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Preconnected) (hcore : 2 ≤ (core G).card) {v : V} (hv : v ∈ core G) :
    (coreNeighbors G v).Nonempty := by
  by_contra hnone
  have hN : coreNeighbors G v = ∅ := not_nonempty_iff_eq_empty.mp hnone
  let S := insert v (G.neighborFinset v)
  have hclosed : ∀ u ∈ S, ∀ w, G.Adj u w → w ∈ S := by
    intro u hu w huw
    rcases mem_insert.mp hu with rfl | huN
    · exact mem_insert_of_mem ((mem_neighborFinset _ _ _).mpr huw)
    · have hvu : G.Adj v u := (mem_neighborFinset _ _ _).mp huN
      have huleaf : u ∈ leaves G := by
        by_contra hbad
        have huK : u ∈ core G := mem_core.mpr (by simpa using hbad)
        have : u ∈ coreNeighbors G v := mem_coreNeighbors.mpr ⟨hvu, huK⟩
        simp [hN] at this
      have hwv := leaf_neighbor_unique G huleaf huw hvu.symm
      subst w
      exact mem_insert_self _ _
  have hSuniv := closed_set_eq_univ G hG S (by exact ⟨v, mem_insert_self _ _⟩) hclosed
  have hKsub : core G ⊆ {v} := by
    intro w hw
    have hwS : w ∈ S := by rw [hSuniv]; exact mem_univ _
    rcases mem_insert.mp hwS with rfl | hwN
    · exact mem_singleton_self _
    · have hwK : w ∈ coreNeighbors G v := mem_coreNeighbors.mpr ⟨(mem_neighborFinset _ _ _).mp hwN, hw⟩
      simp [hN] at hwK
  have hc := card_le_card hKsub
  simp only [card_singleton] at hc
  omega

end TotalDominationAnnihilationProof

#print axioms TotalDominationAnnihilationProof.core_neighbor_nonempty
