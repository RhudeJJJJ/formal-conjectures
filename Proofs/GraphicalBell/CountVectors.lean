import Proofs.GraphicalBell.QuasiGraph

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

lemma countVector_isolate_step {G : SimpleGraph V} {S T : Finset V}
    (hzero : count G T 0 = 0)
    (hrec : ∀ k, count G T (k + 1) = count G S k + (k + 1) * count G S (k + 1)) :
    countVector G T = step 0 (countVector G S) := by
  funext k
  cases k with
  | negSucc n => simp [countVector, step]
  | ofNat n =>
      cases n with
      | zero => simp [countVector, step, hzero]
      | succ n =>
          have hk : ((n + 1 : ℕ) : Int) - 1 = n := by omega
          simp [countVector, step, hk, hrec, Int.natCast_add, Int.natCast_mul]

lemma countVector_partial (q r : ℕ) (hr : r ≤ q) :
    countVector (quasiGraph q r) (range (q + 1)) = step (r : Int) (basis q) := by
  have hzero : count (quasiGraph q r) (range (q + 1)) 0 = 0 :=
    count_zero_of_nonempty (by exact ⟨0, mem_range.mpr (by omega)⟩)
  funext k
  cases k with
  | negSucc n => simp [countVector, step, basis]
  | ofNat n =>
      cases n with
      | zero => simp [countVector, step, basis, hzero]
      | succ n =>
          have hk : ((n + 1 : ℕ) : Int) - 1 = n := by omega
          by_cases hn : n + 1 = q
          · have hrd : r ≤ n + 1 := by omega
            simp [countVector, step, basis, count_quasi_partial q r n hr,
              hk, hn, Int.ofNat_sub hrd]
          · simp [countVector, step, basis, count_quasi_partial q r n hr, hk, hn]

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
        have hrec := count_quasi_isolate q r (q + 1 + t) hr (by omega)
        have heq := countVector_isolate_step hzero hrec
        rw [ih] at heq
        simpa only [Nat.add_succ, tower] using heq
  rw [main, ← step_tower]
  rfl

end GraphicalBellProof
