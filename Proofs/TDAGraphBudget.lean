import Proofs.TDAGeneralBound
import Proofs.TDADegreeBudget

/-! Applying the exact finite degree budget to the full graph covering bound. -/

namespace TotalDominationAnnihilationProof
open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

def degreeTwo (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  univ.filter fun v => G.degree v = 2

def lowVertices (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  univ.filter fun v => G.degree v ≤ 2

theorem low_vertices_partition (G : SimpleGraph V) [DecidableRel G.Adj]
    (hpos : ∀ v, 0 < G.degree v) :
    lowVertices G = leaves G ∪ degreeTwo G := by
  ext v
  simp only [lowVertices, leaves, degreeTwo, mem_filter, mem_union, mem_univ, true_and]
  have hp := hpos v
  omega

theorem leaves_disjoint_degreeTwo (G : SimpleGraph V) [DecidableRel G.Adj] :
    Disjoint (leaves G) (degreeTwo G) := by
  apply Finset.disjoint_left.mpr
  intro v hvP hvB
  have h1 := mem_leaves.mp hvP
  have h2 := (mem_filter.mp hvB).2
  omega

theorem sum_leaves_degree (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∑ v ∈ leaves G, G.degree v) = (leaves G).card := by
  calc
    _ = ∑ _v ∈ leaves G, (1 : ℕ) := sum_congr rfl (fun v hv => mem_leaves.mp hv)
    _ = _ := by simp

theorem sum_degreeTwo (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∑ v ∈ degreeTwo G, G.degree v) = 2 * (degreeTwo G).card := by
  calc
    _ = ∑ _v ∈ degreeTwo G, (2 : ℕ) := sum_congr rfl (fun v hv => (mem_filter.mp hv).2)
    _ = _ := by simp [Nat.mul_comm]

theorem low_vertices_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (hpos : ∀ v, 0 < G.degree v) :
    (∑ v ∈ lowVertices G, G.degree v) = (leaves G).card + 2 * (degreeTwo G).card := by
  rw [low_vertices_partition G hpos, sum_union (leaves_disjoint_degreeTwo G),
    sum_leaves_degree, sum_degreeTwo]

/-- The high-cutoff branch, stated directly as a degree-budget condition. -/
theorem total_domination_le_annihilation_of_low_budget (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : G.Connected) (hn : 3 ≤ Fintype.card V)
    (hbudget : ∑ v ∈ lowVertices G, G.degree v ≤ G.edgeFinset.card) :
    G.totalDominationNumber ≤ G.annihilationNumber := by
  classical
  let : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hpos := hG.preconnected.degree_pos_of_nontrivial
  have hhigh : ∀ v ∈ univ \ lowVertices G, 3 ≤ G.degree v := by
    intro v hv
    have hnot := (mem_sdiff.mp hv).2
    simp only [lowVertices, mem_filter, mem_univ, true_and] at hnot
    omega
  obtain ⟨A, _, hAbudget, hAcard⟩ := exists_rounded_budget univ (lowVertices G)
    (fun v => G.degree v) G.edgeFinset.card (subset_univ _) G.sum_degrees_eq_twice_card_edges
    hbudget hhigh
  have hAc := card_le_annihilationNumber G A hAbudget
  have hlowcard : (lowVertices G).card = (leaves G).card + (degreeTwo G).card := by
    rw [low_vertices_partition G hpos, card_union_of_disjoint (leaves_disjoint_degreeTwo G)]
  have hhighcard := card_sdiff_add_card_eq_card (subset_univ (lowVertices G))
  simp only [card_univ] at hhighcard
  rw [low_vertices_sum G hpos, hlowcard] at hAcard
  have hcover := total_domination_general_bound G hG hn
  change 6 * G.totalDominationNumber ≤ 3 * Fintype.card V + 2 * (leaves G).card +
    (degreeTwo G).card at hcover
  omega

/-- Leaf degrees alone fit the budget because leaf neighborhoods are disjoint edges. -/
theorem leaves_card_le_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Preconnected) (hn : 3 ≤ Fintype.card V) :
    (leaves G).card ≤ G.edgeFinset.card := by
  classical
  have hl := sum_leaf_neighbors G hG hn
  have hpoint : ∀ v ∈ core G, (leafNeighbors G v).card ≤ G.degree v := by
    intro v _
    have h := degree_core_add_leaf G v
    omega
  have hsum := sum_le_sum hpoint
  have hpartition := sum_sdiff (subset_univ (leaves G)) (f := fun v => G.degree v)
  change (∑ v ∈ core G, G.degree v) + (∑ v ∈ leaves G, G.degree v) =
    ∑ v, G.degree v at hpartition
  rw [sum_leaves_degree, G.sum_degrees_eq_twice_card_edges] at hpartition
  omega

/-- The low-cutoff branch supplies the exact arithmetic bound used for trees. -/
theorem edges_add_leaves_le_twice_annihilation_add_one (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : G.Connected) (hn : 3 ≤ Fintype.card V)
    (hlarge : G.edgeFinset.card < ∑ v ∈ lowVertices G, G.degree v) :
    G.edgeFinset.card + (leaves G).card ≤ 2 * G.annihilationNumber + 1 := by
  classical
  let : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hpos := hG.preconnected.degree_pos_of_nontrivial
  have hl := leaves_card_le_edges G hG.preconnected hn
  rw [low_vertices_sum G hpos] at hlarge
  let t := (G.edgeFinset.card - (leaves G).card) / 2
  have ht : t ≤ (degreeTwo G).card := by dsimp [t]; omega
  obtain ⟨T, hTB, hTc⟩ := exists_subset_card_eq ht
  have hdis : Disjoint (leaves G) T :=
    disjoint_of_subset_right hTB (leaves_disjoint_degreeTwo G)
  have hTsum : (∑ v ∈ T, G.degree v) = 2 * t := by
    calc
      _ = ∑ _v ∈ T, (2 : ℕ) := sum_congr rfl (fun v hv => (mem_filter.mp (hTB hv)).2)
      _ = _ := by simp [hTc, Nat.mul_comm]
  have hA : ∑ v ∈ leaves G ∪ T, G.degree v ≤ G.edgeFinset.card := by
    rw [sum_union hdis, sum_leaves_degree, hTsum]
    dsimp [t]
    omega
  have hAc := card_le_annihilationNumber G (leaves G ∪ T) hA
  rw [card_union_of_disjoint hdis, hTc] at hAc
  dsimp [t] at hAc
  omega

end TotalDominationAnnihilationProof

#print axioms TotalDominationAnnihilationProof.total_domination_le_annihilation_of_low_budget
#print axioms TotalDominationAnnihilationProof.edges_add_leaves_le_twice_annihilation_add_one
