/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerWeightedBernstein

namespace Gebendorfer.RadenkovicGutman.IntegerBernsteinTable
open NestedInteger IntegerWeightedBernstein
set_option maxHeartbeats 0

/-- Bernstein scalar weights depend on the list length, never on its physical
coefficient data. Different cells keep all their separate identities and signs. -/
theorem weights_length {n : ℕ} (D j k : ℕ) (p : Poly (n+1)) :
    weights (n := n) D j k p=weights (n := 0) D j k (List.replicate p.length (0 : ℤ)) := by
  induction p generalizing k with
  | nil => rfl
  | cons c p ih =>
    simp only [List.length_cons,List.replicate_succ]
    change (if k ≤ j then some (Nat.fast_choose (D-k) (j-k) : ℤ) else none) ::
        weights (n := n) D j (k+1) p =
      (if k ≤ j then some (Nat.fast_choose (D-k) (j-k) : ℤ) else none) ::
        weights (n := 0) D j (k+1) (List.replicate p.length (0 : ℤ))
    exact congrArg (List.cons _) (ih (k+1))

theorem checked {n : ℕ} (D j k N : ℕ) (p : Poly (n+1)) (row : List (Option ℤ))
    (hN : p.length=N)
    (hrow : row=weights (n := 0) D j k (List.replicate N (0 : ℤ))) :
    row=weights (n := n) D j k p := by
  have h := weights_length (n := n) D j k p
  rw [hN] at h
  exact hrow.trans h.symm

#print axioms weights_length
#print axioms checked
end Gebendorfer.RadenkovicGutman.IntegerBernsteinTable
