import Proofs.GraphicalBell.Parameters
import Proofs.GraphicalBell.Vectors

/-! Coefficient comparison for the finite-order, finite-size candidate model. -/

namespace GraphicalBellProof
open PHOEG.GraphicalBell

noncomputable def model (n m : ℕ) : Vector :=
  if cliqueOrder n m = n then basis n else
    candidate (cliqueOrder n m) (m - (cliqueOrder n m).choose 2) (n - cliqueOrder n m - 1)

lemma candidate_support (q r t : ℕ) (k : Int) (hk : k < q) : candidate q r t k = 0 := by
  simp [candidate, step, lower_support q t k hk, lower_support q t (k - 1) (by omega)]

lemma model_support (n m : ℕ) (k : Int) (hk : k < cliqueOrder n m) : model n m k = 0 := by
  unfold model
  split
  next h => simp [basis, show k ≠ (n : Int) by omega]
  next _ => exact candidate_support _ _ _ k hk

lemma model_step {n m d : ℕ} (hn : 1 ≤ n) (hm : m ≤ n.choose 2)
    (hd : d ≤ cliqueOrder n m - 1) (hdm : d ≤ m)
    (hm' : m - d ≤ (n - 1).choose 2) (k : Int) :
    model n m k ≤ step (d : Int) (model (n - 1) (m - d)) k := by
  let q := cliqueOrder n m
  let r := m - q.choose 2
  have hqpos : 1 ≤ q := clique_param_pos n m hn
  have hqn : q ≤ n := clique_param_le n m
  have hsum : m = q.choose 2 + r := clique_decomposition n m
  by_cases hfull : q = n
  · have hmfull : m = n.choose 2 := clique_complete_remainder hm hfull
    have hnchoose : n.choose 2 = (n - 1).choose 2 + (n - 1) := by
      have h := choose_succ_two (n - 1)
      simpa only [Nat.sub_add_cancel hn] using h
    have hdn : d = n - 1 := by change d ≤ q - 1 at hd; omega
    have hmnew : m - d = (n - 1).choose 2 := by omega
    have hqnew : cliqueOrder (n - 1) (m - d) = n - 1 :=
      Nat.findGreatest_eq (by rw [hmnew])
    have hold : model n m = basis n := by simp [model, show cliqueOrder n m = n from hfull]
    have hnew : model (n - 1) (m - d) = basis (n - 1) := by simp [model, hqnew]
    rw [hold, hnew, hdn, step_basis]
    have he : n - 1 + 1 = n := by omega
    rw [he]
  · have hq : q < n := by omega
    by_cases hsmall : d ≤ r
    · have hqnew : cliqueOrder (n - 1) (m - d) = q := clique_after_small_deletion hq hsmall
      by_cases hboundary : n = q + 1
      · have hdr : d = r := by
          have : n - 1 = q := by omega
          rw [this] at hm'
          omega
        have hnew : model (n - 1) (m - d) = basis q := by
          unfold model
          rw [hqnew, if_pos (show q = n - 1 by omega)]
          congr 1
          omega
        have hold : model n m = step (r : Int) (basis q) := by
          have ht : n - q - 1 = 0 := by omega
          simp [model, show cliqueOrder n m = q from rfl, hfull, ht, candidate, tower, r]
        rw [hold, hnew, hdr]
      · have hqnewlt : q < n - 1 := by omega
        have hrnew : (m - d) - q.choose 2 = r - d := by omega
        let t := (n - 1) - q - 1
        have ht : n - q - 1 = t + 1 := by dsimp [t]; omega
        have hold : model n m = candidate q r (t + 1) := by
          simp [model, show cliqueOrder n m = q from rfl, hfull, ht, r]
        have hnew : model (n - 1) (m - d) = candidate q (r - d) t := by
          simp [model, hqnew, show q ≠ n - 1 by omega, hrnew, t]
        rw [hold, hnew]
        exact compare_same_clique q r d t hsmall k
    · have hr : r < d := by omega
      have hqnew : cliqueOrder (n - 1) (m - d) = q - 1 :=
        clique_after_large_deletion hn hd hr
      have hchoose : q.choose 2 = (q - 1).choose 2 + (q - 1) := by
        have h := choose_succ_two (q - 1)
        simpa only [Nat.sub_add_cancel hqpos] using h
      have hrnew : (m - d) - (q - 1).choose 2 = q - 1 - d + r := by omega
      have ht : (n - 1) - (q - 1) - 1 = n - q - 1 := by omega
      have hold : model n m = candidate q r (n - q - 1) := by
        simp [model, show cliqueOrder n m = q from rfl, hfull, r]
      have hnew : model (n - 1) (m - d) = candidate (q - 1) (q - 1 - d + r) (n - q - 1) := by
        simp [model, hqnew, show q - 1 ≠ n - 1 by omega, hrnew, ht]
      rw [hold, hnew]
      have h := compare_previous_clique (q - 1) r d (n - q - 1) hd hr k
      simpa only [Nat.sub_add_cancel hqpos] using h

end GraphicalBellProof
