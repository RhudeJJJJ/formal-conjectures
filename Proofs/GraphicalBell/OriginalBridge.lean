import Proofs.GraphicalBell.CountVectors
import Proofs.GraphicalBell.Transport
import Proofs.GraphicalBell.BellBridge
import Proofs.GraphicalBell.Model
import Proofs.GraphicalBell.Degrees
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

namespace GraphicalBellProof
open Finset SimpleGraph PHOEG.GraphicalBell

lemma sizeOn_univ {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : sizeOn G univ = G.edgeFinset.card := by
  classical
  have hdegree : ∀ v, degreeOn G univ v = G.degree v := by
    intro v
    unfold degreeOn SimpleGraph.degree
    apply congrArg Finset.card
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, SimpleGraph.mem_neighborFinset]
  unfold sizeOn degreeSum
  simp only [hdegree]
  rw [G.sum_degrees_eq_twice_card_edges]
  omega

lemma candidate_transport (n m k : ℕ) :
    count (quasiComplete n m) univ k =
      count (quasiGraph (cliqueOrder n m) (m - (cliqueOrder n m).choose 2)) (range n) k := by
  let q := cliqueOrder n m
  let r := m - q.choose 2
  have hr : ∀ u v : Fin n,
      (quasiComplete n m).Adj u v ↔ (quasiGraph q r).Adj u.val v.val := by
    intro u v
    change (u ≠ v ∧ _) ↔ (u.val ≠ v.val ∧ _)
    constructor
    · rintro ⟨hne, h⟩
      exact ⟨fun he => hne (Fin.ext he), h⟩
    · rintro ⟨hne, h⟩
      exact ⟨fun he => hne (congrArg Fin.val he), h⟩
  have himage : (univ : Finset (Fin n)).image Fin.val = range n := by
    ext x
    constructor
    · intro hx
      obtain ⟨u, _, rfl⟩ := mem_image.mp hx
      exact mem_range.mpr u.isLt
    · intro hx
      exact mem_image.mpr ⟨⟨x, mem_range.mp hx⟩, mem_univ _, rfl⟩
  have h := count_transport (f := Fin.val) Fin.val_injective hr univ k
  simpa only [himage] using h

lemma original_model (n m k : ℕ) :
    model n m (k : Int) = (PHOEG.GraphicalBell.stirling (quasiComplete n m) k : Int) := by
  let q := cliqueOrder n m
  let r := m - q.choose 2
  by_cases hfull : q = n
  · have hc : ∀ u ∈ (univ : Finset (Fin n)), ∀ v ∈ univ, u ≠ v →
        (quasiComplete n m).Adj u v := by
      intro u _ v _ hne
      exact ⟨hne, Or.inl ⟨by change u.val < q; rw [hfull]; exact u.isLt,
        by change v.val < q; rw [hfull]; exact v.isLt⟩⟩
    have hcount := count_complete hc k
    simp only [card_univ, Fintype.card_fin] at hcount
    rw [original_stirling_eq_count, hcount]
    simp [model, show cliqueOrder n m = n from hfull, basis]
  · have hqn := clique_param_le n m
    have hq : q < n := by omega
    have hr : r ≤ q := Nat.le_of_lt (clique_remainder_lt hq)
    have hshape : q + 1 + (n - q - 1) = n := by omega
    have hv := congrFun (countVector_quasi q r (n - q - 1) hr) (k : Int)
    have he : (count (quasiGraph q r) (range n) k : Int) = candidate q r (n - q - 1) (k : Int) := by
      rw [countVector_nat] at hv
      rw [hshape] at hv
      exact hv
    rw [original_stirling_eq_count, candidate_transport]
    simpa [model, show cliqueOrder n m = q from rfl, hfull, r] using he.symm

end GraphicalBellProof
