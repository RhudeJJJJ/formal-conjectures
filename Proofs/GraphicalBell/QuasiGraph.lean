import Proofs.GraphicalBell.Discrete
import Proofs.GraphicalBell.Simplicial
import Proofs.GraphicalBell.Vectors

namespace GraphicalBellProof
open Finset SimpleGraph

def quasiGraph (q r : ℕ) : SimpleGraph ℕ where
  Adj u v := u ≠ v ∧ ((u < q ∧ v < q) ∨ (u = q ∧ v < r) ∨ (v = q ∧ u < r))
  symm := ⟨by
    intro u v h
    refine ⟨Ne.symm h.1, ?_⟩
    rcases h.2 with h | h | h
    · exact Or.inl ⟨h.2, h.1⟩
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)⟩
  loopless := ⟨by intro v h; exact h.1 rfl⟩

lemma quasi_clique (q r : ℕ) :
    ∀ x ∈ range q, ∀ y ∈ range q, x ≠ y → (quasiGraph q r).Adj x y := by
  intro x hx y hy hxy
  exact ⟨hxy, Or.inl ⟨mem_range.mp hx, mem_range.mp hy⟩⟩

lemma quasi_partial_degree (q r : ℕ) (hr : r ≤ q) :
    degreeOn (quasiGraph q r) (range q) q = r := by
  classical
  unfold degreeOn
  have h : (range q).filter ((quasiGraph q r).Adj q) = range r := by
    ext x
    simp only [mem_filter, mem_range, quasiGraph]
    constructor
    · rintro ⟨hx, hne, h | h | h⟩
      · omega
      · exact h.2
      · omega
    · intro hx
      exact ⟨by omega, by omega, Or.inr (Or.inl ⟨by trivial, hx⟩)⟩
  rw [h, card_range]

lemma quasi_partial_simplicial (q r : ℕ) :
    ∀ x ∈ range q, (quasiGraph q r).Adj q x →
      ∀ y ∈ range q, (quasiGraph q r).Adj q y → x ≠ y → (quasiGraph q r).Adj x y := by
  intro x hx _ y hy _ hxy
  exact quasi_clique q r x hx y hy hxy

lemma quasi_isolated (q r v : ℕ) (hr : r ≤ q) (hv : q < v) :
    ∀ w, ¬ (quasiGraph q r).Adj v w := by
  intro w h
  change v ≠ w ∧ ((v < q ∧ w < q) ∨ (v = q ∧ w < r) ∨ (w = q ∧ v < r)) at h
  rcases h.2 with h | h | h <;> omega

lemma degreeOn_isolated (G : SimpleGraph ℕ) (S : Finset ℕ) (v : ℕ)
    (hv : ∀ w, ¬ G.Adj v w) : degreeOn G S v = 0 := by
  classical
  simp [degreeOn, hv]

lemma range_insert (q : ℕ) : insert q (range q) = range (q + 1) := by
  ext x
  simp only [mem_insert, mem_range]
  omega

lemma count_quasi_clique (q r k : ℕ) :
    count (quasiGraph q r) (range q) k = if k = q then 1 else 0 := by
  simpa only [card_range] using count_complete (quasi_clique q r) k

lemma count_quasi_partial (q r k : ℕ) (hr : r ≤ q) :
    count (quasiGraph q r) (range (q + 1)) (k + 1) =
      (if k = q then 1 else 0) + (k + 1 - r) * (if k + 1 = q then 1 else 0) := by
  rw [← range_insert]
  rw [simplicial_recurrence (notMem_range_self) (quasi_partial_simplicial q r) k,
    quasi_partial_degree q r hr, count_quasi_clique, count_quasi_clique]

lemma count_quasi_isolate (q r n k : ℕ) (hr : r ≤ q) (hn : q < n) :
    count (quasiGraph q r) (range (n + 1)) (k + 1) =
      count (quasiGraph q r) (range n) k +
        (k + 1) * count (quasiGraph q r) (range n) (k + 1) := by
  have hnot := quasi_isolated q r n hr hn
  rw [← range_insert]
  rw [simplicial_recurrence (notMem_range_self) (by
    intro x _ hx
    exact (hnot x hx).elim) k, degreeOn_isolated _ _ _ hnot]
  simp

end GraphicalBellProof
