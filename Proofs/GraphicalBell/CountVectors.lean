import Proofs.GraphicalBell.QuasiGraph
import Mathlib.Algebra.Order.Ring.Int

namespace GraphicalBellProof
open Finset SimpleGraph
variable {V : Type*} [DecidableEq V]

lemma count_zero_of_nonempty {G : SimpleGraph V} {S : Finset V} (hS : S.Nonempty) :
    count G S 0 = 0 := by
  let : IsEmpty (Graded G S 0) := ⟨fun P => by
    have hp : P.val.val = ∅ := card_eq_zero.mp P.property
    have hs : S = ∅ := by simpa [hp] using P.val.property.2.2.symm
    exact hS.ne_empty hs⟩
  simp [count]

noncomputable def countVector (G : SimpleGraph V) (S : Finset V) : Vector :=
  fun k => if k < 0 then 0 else (count G S k.toNat : Int)

lemma countVector_nat (G : SimpleGraph V) (S : Finset V) (n : ℕ) :
    countVector G S (n : Int) = (count G S n : Int) := by
  simp [countVector, show ¬ (n : Int) < 0 by omega]

lemma countVector_isolate_step {G : SimpleGraph V} {S T : Finset V}
    (hzero : count G T 0 = 0)
    (hrec : ∀ k, count G T (k + 1) = count G S k + (k + 1) * count G S (k + 1)) :
    countVector G T = step 0 (countVector G S) := by
  funext k
  cases k with
  | negSucc n => simp [countVector, step]
  | ofNat n =>
      cases n with
      | zero =>
          rw [countVector_nat, hzero]
          simp [step, countVector]
      | succ n =>
          have hk : ((n + 1 : ℕ) : Int) - 1 = n := by omega
          rw [countVector_nat]
          unfold step
          rw [hk, countVector_nat, countVector_nat]
          simpa using congrArg (fun m : ℕ => (m : Int)) (hrec n)

lemma countVector_partial (q r : ℕ) (hr : r ≤ q) :
    countVector (quasiGraph q r) (range (q + 1)) = step (r : Int) (basis q) := by
  have hzero : count (quasiGraph q r) (range (q + 1)) 0 = 0 :=
    count_zero_of_nonempty (by exact ⟨0, mem_range.mpr (by omega)⟩)
  funext k
  cases k with
  | negSucc n => simp [countVector, step, basis]
  | ofNat n =>
      cases n with
      | zero =>
          rw [countVector_nat, hzero]
          unfold step basis
          simp only [if_neg (show (-1 : Int) ≠ q by omega), Int.zero_add]
          by_cases hq : (0 : Int) = q
          · rw [if_pos hq]
            have hr0 : r = 0 := by omega
            simp [hr0]
          · rw [if_neg hq]
            simp
      | succ n =>
          have hk : ((n + 1 : ℕ) : Int) - 1 = n := by omega
          rw [countVector_nat, count_quasi_partial q r n hr]
          unfold step
          rw [hk]
          unfold basis
          have he0 : ((n : Int) = (q : Int)) ↔ n = q := by omega
          have he1 : (((n + 1 : ℕ) : Int) = (q : Int)) ↔ n + 1 = q := by omega
          simp only [he0, he1]
          by_cases hn : n + 1 = q
          · have hnp : n ≠ q := by omega
            have hrd : r ≤ n + 1 := by omega
            simpa [hn, hnp] using (Int.ofNat_sub hrd)
          · by_cases hp : n = q
            · simp [hn, hp]
            · simp [hn, hp]

lemma countVector_quasi (q r t : ℕ) (hr : r ≤ q) :
    countVector (quasiGraph q r) (range (q + 1 + t)) = candidate q r t := by
  have main : ∀ t, countVector (quasiGraph q r) (range (q + 1 + t)) =
      tower (step (r : Int) (basis q)) t := by
    intro t
    induction t with
    | zero => simpa [tower] using countVector_partial q r hr
    | succ t ih =>
        have hzero : count (quasiGraph q r) (range (q + 1 + t + 1)) 0 = 0 :=
          count_zero_of_nonempty ⟨0, mem_range.mpr (by omega)⟩
        have hrec := fun k => count_quasi_isolate q r (q + 1 + t) k hr (by omega)
        have heq := countVector_isolate_step hzero hrec
        rw [ih] at heq
        simpa [Nat.add_assoc, tower] using heq
  change countVector (quasiGraph q r) (range (q + 1 + t)) =
    step (r : Int) (tower (basis q) t)
  rw [main]
  exact (step_tower (r : Int) (basis q) t).symm

end GraphicalBellProof
