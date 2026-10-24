module
/-
Copyright 2026 Jonas J. Gebendorfer. Apache 2.0.
Complete root isolation from exact signs on ordered disjoint intervals.
The degree bound certifies that no additional real root is omitted.
-/
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Tactic

@[expose] public section

namespace Gebendorfer.RadenkovicGutman.RootIsolation
open Polynomial Set Finset
open scoped Classical
noncomputable section

theorem root_between (p : ℝ[X]) (a b : ℝ) (hab : a < b)
    (hsign : p.eval a * p.eval b < 0) :
    ∃ x ∈ Ioo a b, p.eval x = 0 := by
  rcases mul_neg_iff.mp hsign with h | h
  · obtain ⟨x, hx, hp⟩ := intermediate_value_Ioo' hab.le p.continuous.continuousOn ⟨h.2, h.1⟩
    exact ⟨x, hx, hp⟩
  · obtain ⟨x, hx, hp⟩ := intermediate_value_Ioo hab.le p.continuous.continuousOn h
    exact ⟨x, hx, hp⟩

theorem complete_roots (p : ℝ[X]) (hp : p ≠ 0) (n : ℕ)
    (hn : p.natDegree ≤ n) (a b : Fin n → ℝ)
    (hab : ∀ i, a i < b i) (hsign : ∀ i, p.eval (a i) * p.eval (b i) < 0)
    (horder : ∀ i j, i < j → b i ≤ a j) :
    ∃ r : Fin n → ℝ, (∀ i, r i ∈ Ioo (a i) (b i)) ∧
      p.roots = Multiset.map r (Finset.univ : Finset (Fin n)).val := by
  choose r hrmem hrroot using (fun i => root_between p (a i) (b i) (hab i) (hsign i))
  have hrmono : StrictMono r := by
    intro i j hij
    exact (hrmem i).2.trans_le (horder i j hij) |>.trans (hrmem j).1
  let embedding : Fin n ↪ ℝ := ⟨r, hrmono.injective⟩
  let roots : Finset ℝ := Finset.univ.map embedding
  have hroots (x : ℝ) (hx : x ∈ roots) : p.eval x = 0 := by
    obtain ⟨i, _, hi⟩ := Finset.mem_map.mp hx
    subst x
    exact hrroot i
  have hcard : p.natDegree ≤ roots.card := by simpa [roots] using hn
  have he := Polynomial.roots_eq_of_natDegree_le_card_of_ne_zero hroots hcard hp
  exact ⟨r, hrmem, he⟩

theorem stop_loss_bounds (p : ℝ[X]) (hp : p ≠ 0) (n : ℕ)
    (hn : p.natDegree ≤ n) (a b : Fin n → ℝ)
    (hab : ∀ i, a i < b i) (hsign : ∀ i, p.eval (a i) * p.eval (b i) < 0)
    (horder : ∀ i j, i < j → b i ≤ a j) (α : ℝ) :
    (∑ i, max (a i - α) 0) ≤ (p.roots.map (fun x => max (x - α) 0)).sum ∧
      (p.roots.map (fun x => max (x - α) 0)).sum ≤ ∑ i, max (b i - α) 0 := by
  obtain ⟨r, hr, he⟩ := complete_roots p hp n hn a b hab hsign horder
  have hs : (p.roots.map (fun x => max (x - α) 0)).sum = ∑ i, max (r i - α) 0 := by
    rw [he, Multiset.map_map]
    rfl
  rw [hs]
  constructor
  · apply Finset.sum_le_sum
    intro i _
    exact max_le_max (sub_le_sub_right (hr i).1.le α) le_rfl
  · apply Finset.sum_le_sum
    intro i _
    exact max_le_max (sub_le_sub_right (hr i).2.le α) le_rfl

#print axioms root_between
#print axioms complete_roots
#print axioms stop_loss_bounds
end
end Gebendorfer.RadenkovicGutman.RootIsolation
