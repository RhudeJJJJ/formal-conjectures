import Proofs.GraphicalBell.Model
import Proofs.GraphicalBell.Degrees
import Proofs.GraphicalBell.Base
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Tactic.NormNum

namespace GraphicalBellProof
open Finset SimpleGraph PHOEG.GraphicalBell
variable {V : Type*} [DecidableEq V]

lemma model_le_count (G : SimpleGraph V) (S : Finset V) :
    ∀ k : ℕ, model S.card (sizeOn G S) (k : Int) ≤ (count G S k : Int) := by
  induction S using Finset.strongInductionOn with
  | h S ih =>
      intro k
      by_cases hS : S = ∅
      · subst S
        simp [model, sizeOn, degreeSum, cliqueOrder, basis, count_empty]
      have hnonempty : S.Nonempty := nonempty_iff_ne_empty.mpr hS
      let n := S.card
      let m := sizeOn G S
      let q := cliqueOrder n m
      have hn : 1 ≤ n := card_pos.mpr hnonempty
      have hm : m ≤ n.choose 2 := sizeOn_le G S
      have hqpos : 1 ≤ q := clique_param_pos n m hn
      have hqn : q ≤ n := clique_param_le n m
      obtain ⟨v, hv, hdlt⟩ : ∃ v ∈ S, degreeOn G S v < q := by
        by_cases hq : q < n
        · exact exists_small_degree hq (clique_param_next hq)
        · obtain ⟨v, hv⟩ := hnonempty
          exact ⟨v, hv, by have h := degreeOn_le (G := G) hv; omega⟩
      let R := S.erase v
      let d := degreeOn G R v
      have hvr : v ∉ R := notMem_erase _ _
      have hSR : insert v R = S := insert_erase hv
      have hnr : R.card = n - 1 := card_erase_of_mem hv
      have hds : degreeOn G S v = d := by
        have h := degreeOn_insert (G := G) hvr v
        rw [hSR] at h
        simpa only [if_neg (G.loopless.irrefl v), Nat.add_zero] using h
      have hmadd : m = sizeOn G R + d := by
        have h := sizeOn_insert (G := G) hvr
        rwa [hSR] at h
      have hdm : d ≤ m := by omega
      have hmr : m - d = sizeOn G R := by omega
      have hmrbound : m - d ≤ (n - 1).choose 2 := by
        rw [hmr, ← hnr]
        exact sizeOn_le G R
      have hd : d ≤ cliqueOrder n m - 1 := by change d ≤ q - 1; omega
      have hIH : ∀ j : ℕ, model (n - 1) (m - d) (j : Int) ≤ (count G R j : Int) := by
        intro j
        have h := ih R (erase_ssubset hv) j
        simpa only [hnr, hmr] using h
      cases k with
      | zero =>
          have hz : model n m (0 : Int) = 0 := model_support n m 0 (by omega)
          change model n m 0 ≤ _
          rw [hz]
          omega
      | succ j =>
          have hstep := model_step hn hm hd hdm hmrbound ((j + 1 : ℕ) : Int)
          have hdel := deletion_lower (G := G) hvr j
          rw [hSR] at hdel
          change count G R j + (j + 1 - d) * count G R (j + 1) ≤ count G S (j + 1) at hdel
          have hdelInt : ((count G R j + (j + 1 - d) * count G R (j + 1) : ℕ) : Int) ≤
              (count G S (j + 1) : Int) := by exact_mod_cast hdel
          have hj : ((j + 1 : ℕ) : Int) - 1 = (j : Int) := by omega
          change model n m ((j + 1 : ℕ) : Int) ≤ _
          by_cases hdk : d ≤ j + 1
          · calc
              model n m ((j + 1 : ℕ) : Int) ≤
                  step (d : Int) (model (n - 1) (m - d)) ((j + 1 : ℕ) : Int) := hstep
              _ ≤ (count G R j : Int) + (((j + 1 : ℕ) : Int) - d) *
                  (count G R (j + 1) : Int) := by
                    unfold step
                    rw [hj]
                    exact add_le_add (hIH j) (mul_le_mul_of_nonneg_left (hIH (j + 1)) (by omega))
              _ = ((count G R j + (j + 1 - d) * count G R (j + 1) : ℕ) : Int) := by
                    rw [Int.natCast_add, Int.natCast_mul, Int.ofNat_sub hdk]
              _ ≤ (count G S (j + 1) : Int) := hdelInt
          · have hqd := clique_after_deletion_ge hn hd
            have hz : model (n - 1) (m - d) ((j + 1 : ℕ) : Int) = 0 :=
              model_support _ _ _ (by omega)
            have hcoef : j + 1 - d = 0 := by omega
            calc
              model n m ((j + 1 : ℕ) : Int) ≤
                  step (d : Int) (model (n - 1) (m - d)) ((j + 1 : ℕ) : Int) := hstep
              _ = model (n - 1) (m - d) (j : Int) := by simp [step, hz, hj]
              _ ≤ (count G R j : Int) := hIH j
              _ ≤ (count G S (j + 1) : Int) := by
                  simpa only [hcoef, Nat.zero_mul, Nat.add_zero] using hdelInt

end GraphicalBellProof
