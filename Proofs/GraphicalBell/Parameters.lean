import FormalConjectures.Other.GraphicalBell
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Choose.Basic
import Lean.Elab.Tactic.Omega

/-! Clique and remainder parameters under deletion of a minimum-degree vertex. -/

namespace GraphicalBellProof
open PHOEG.GraphicalBell

lemma clique_param_le (n m : ℕ) : cliqueOrder n m ≤ n := Nat.findGreatest_le n

lemma clique_param_spec (n m : ℕ) : (cliqueOrder n m).choose 2 ≤ m := by
  exact Nat.findGreatest_spec (P := fun q => q.choose 2 ≤ m) (m := 0)
    (show 0 ≤ n by omega) (show (0 : ℕ).choose 2 ≤ m by change 0 ≤ m; omega)

lemma clique_param_pos (n m : ℕ) (hn : 1 ≤ n) : 1 ≤ cliqueOrder n m := by
  exact Nat.le_findGreatest hn (by simp)

lemma clique_param_mono {n n' m m' : ℕ} (hn : n' ≤ n) (hm : m' ≤ m) :
    cliqueOrder n' m' ≤ cliqueOrder n m := by
  exact Nat.findGreatest_mono (fun _ h => h.trans hm) hn

lemma clique_param_next {n m : ℕ} (hq : cliqueOrder n m < n) :
    m < (cliqueOrder n m + 1).choose 2 := by
  have h := Nat.findGreatest_is_greatest (P := fun q => q.choose 2 ≤ m)
    (show cliqueOrder n m < cliqueOrder n m + 1 by omega)
    (show cliqueOrder n m + 1 ≤ n by omega)
  omega

lemma choose_succ_two (q : ℕ) : (q + 1).choose 2 = q.choose 2 + q := by
  rw [Nat.choose_succ_succ]
  simp [Nat.choose_one_right, Nat.add_comm]

lemma clique_decomposition (n m : ℕ) :
    m = (cliqueOrder n m).choose 2 + (m - (cliqueOrder n m).choose 2) := by
  have h := clique_param_spec n m
  omega

lemma clique_remainder_lt {n m : ℕ} (hq : cliqueOrder n m < n) :
    m - (cliqueOrder n m).choose 2 < cliqueOrder n m := by
  have h := clique_param_next hq
  rw [choose_succ_two] at h
  have hs := clique_param_spec n m
  omega

lemma clique_complete_remainder {n m : ℕ} (hm : m ≤ n.choose 2)
    (hq : cliqueOrder n m = n) : m = n.choose 2 := by
  have hs := clique_param_spec n m
  rw [hq] at hs
  omega

lemma clique_after_small_deletion {n m d : ℕ}
    (hq : cliqueOrder n m < n) (hd : d ≤ m - (cliqueOrder n m).choose 2) :
    cliqueOrder (n - 1) (m - d) = cliqueOrder n m := by
  have hupper := clique_param_mono (show n - 1 ≤ n by omega) (show m - d ≤ m by omega)
  have hs := clique_param_spec n m
  have hlower : cliqueOrder n m ≤ cliqueOrder (n - 1) (m - d) := by
    exact Nat.le_findGreatest (show cliqueOrder n m ≤ n - 1 by omega) (by omega)
  omega

lemma clique_after_large_deletion {n m d : ℕ} (hn : 1 ≤ n)
    (hd : d ≤ cliqueOrder n m - 1) (hr : m - (cliqueOrder n m).choose 2 < d) :
    cliqueOrder (n - 1) (m - d) = cliqueOrder n m - 1 := by
  let q := cliqueOrder n m
  have hqpos : 1 ≤ q := clique_param_pos n m hn
  have hqn : q ≤ n := clique_param_le n m
  have hsum : q.choose 2 = (q - 1).choose 2 + (q - 1) := by
    have h := choose_succ_two (q - 1)
    simpa only [Nat.sub_add_cancel hqpos] using h
  have hs : q.choose 2 ≤ m := clique_param_spec n m
  have hupper : cliqueOrder (n - 1) (m - d) ≤ q :=
    clique_param_mono (by omega) (by omega)
  have hlower : q - 1 ≤ cliqueOrder (n - 1) (m - d) := by
    exact Nat.le_findGreatest (by omega) (by omega)
  have hne : cliqueOrder (n - 1) (m - d) ≠ q := by
    intro he
    have h := clique_param_spec (n - 1) (m - d)
    rw [he] at h
    change m - q.choose 2 < d at hr
    omega
  omega

lemma clique_after_deletion_ge {n m d : ℕ} (hn : 1 ≤ n)
    (hd : d ≤ cliqueOrder n m - 1) : d ≤ cliqueOrder (n - 1) (m - d) := by
  let q := cliqueOrder n m
  have hqpos : 1 ≤ q := clique_param_pos n m hn
  have hqn : q ≤ n := clique_param_le n m
  have hs : q.choose 2 ≤ m := clique_param_spec n m
  have hc : q.choose 2 = (q - 1).choose 2 + (q - 1) := by
    have h := choose_succ_two (q - 1)
    simpa only [Nat.sub_add_cancel hqpos] using h
  have hle : q - 1 ≤ cliqueOrder (n - 1) (m - d) :=
    Nat.le_findGreatest (by omega) (by omega)
  omega

end GraphicalBellProof
