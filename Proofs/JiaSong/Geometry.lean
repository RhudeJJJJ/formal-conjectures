module

public import FormalConjectures.Paper.JiaSongRemoteness

/-! # The actual bowtie graph and its distances

The witness is exactly `JiaSong.twoCliqueJoin 5`. Distances and transmissions
are derived from graph walks, rather than supplied as a replacement matrix.
Source: the order-five counterexample in the manuscript linked by PR7400.
-/

@[expose] public section
namespace JiaSong.Certificate
open SimpleGraph Matrix

abbrev H := twoCliqueJoin 5

instance : DecidableRel H.Adj := fun u v =>
  inferInstanceAs (Decidable (u ≠ v ∧ (u.val = 0 ∨ v.val = 0 ∨
    (u.val ≤ (5 - 1) / 2 ∧ v.val ≤ (5 - 1) / 2) ∨
    ((5 - 1) / 2 < u.val ∧ (5 - 1) / 2 < v.val))))

theorem reachable_zero (v : Fin 5) : H.Reachable v 0 := by
  by_cases hv : v = 0
  · subst v
    exact Reachable.refl _
  · exact (show H.Adj v 0 by simp [H, twoCliqueJoin, hv]).reachable

theorem connected : H.Connected := by
  exact ⟨fun u v => (reachable_zero u).trans (reachable_zero v).symm⟩

theorem edge_count : H.edgeFinset.card = 6 := by decide

theorem dist_formula (u v : Fin 5) :
    H.dist u v = if u = v then 0 else if H.Adj u v then 1 else 2 := by
  classical
  split_ifs with he ha
  · subst v
    exact SimpleGraph.dist_self
  · exact SimpleGraph.dist_eq_one_iff_adj.mpr ha
  · have hu : u ≠ 0 := by
      intro h
      subst u
      exact ha (by simp [H, twoCliqueJoin, he])
    have hv : v ≠ 0 := by
      intro h
      subst v
      exact ha (by simp [H, twoCliqueJoin, he])
    have hu0 : H.Adj u 0 := by simp [H, twoCliqueJoin, hu]
    have h0v : H.Adj 0 v := by simp [H, twoCliqueJoin, Ne.symm hv]
    have hupper : H.dist u v ≤ 2 := by
      simpa using SimpleGraph.dist_le (Walk.cons hu0 (Walk.cons h0v Walk.nil))
    have hlower := connected.one_lt_dist_of_ne_of_not_adj he ha
    omega

theorem distance_matrix : distanceMatrix H =
    !![0, 1, 1, 1, 1;
       1, 0, 1, 2, 2;
       1, 1, 0, 2, 2;
       1, 2, 2, 0, 1;
       1, 2, 2, 1, 0] := by
  ext u v
  change (H.dist u v : ℝ) = _
  rw [dist_formula]
  fin_cases u <;> fin_cases v <;> norm_num [H, twoCliqueJoin]

theorem transmission (v : Fin 5) :
    (∑ w : Fin 5, (H.dist v w : ℝ)) = if v = 0 then 4 else 6 := by
  change (∑ w : Fin 5, distanceMatrix H v w) = _
  rw [distance_matrix]
  fin_cases v <;> norm_num [Fin.sum_univ_succ]

theorem remoteness_value : remoteness H = 3 / 2 := by
  have hm : (3 / 2 : ℝ) ∈ {x : ℝ | ∃ v : Fin 5,
      x = (∑ w : Fin 5, (H.dist v w : ℝ)) / ((Fintype.card (Fin 5) : ℝ) - 1)} := by
    refine ⟨1, ?_⟩
    norm_num [transmission]
  have hu : ∀ x ∈ {x : ℝ | ∃ v : Fin 5,
      x = (∑ w : Fin 5, (H.dist v w : ℝ)) / ((Fintype.card (Fin 5) : ℝ) - 1)},
      x ≤ (3 / 2 : ℝ) := by
    rintro x ⟨v, rfl⟩
    rw [transmission]
    split_ifs <;> norm_num
  exact le_antisymm (csSup_le ⟨_, hm⟩ hu) (le_csSup ⟨_, hu⟩ hm)

end JiaSong.Certificate
