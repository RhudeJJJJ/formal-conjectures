/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerWeightedOuter

namespace Gebendorfer.RadenkovicGutman.IntegerOuterTable
open NestedInteger IntegerWeightedOuter
set_option maxHeartbeats 0

/-- The affine scalar weights depend on length and box coordinates. Sharing
them preserves each cell's coefficient identities and physical cover. -/
theorem weights_length {n : ℕ} (l w D : ℤ) (k : ℕ) (p : Poly (n+1)) :
    weights (n := n) l w D k p =
      weights (n := 0) l w D k (List.replicate p.length (0 : ℤ)) := by
  induction p generalizing k with
  | nil => rfl
  | cons c p ih =>
    simp only [List.length_cons,List.replicate_succ,weights,List.length_replicate]
    exact congrArg (List.cons _) (ih (k+1))

theorem checked {n : ℕ} (l w D : ℤ) (k N : ℕ) (p : Poly (n+1))
    (rows : List (List ℤ)) (hN : p.length=N)
    (hrows : rows=weights (n := 0) l w D k (List.replicate N (0 : ℤ))) :
    rows=weights (n := n) l w D k p := by
  have h := weights_length (n := n) l w D k p
  rw [hN] at h
  exact hrows.trans h.symm

#print axioms weights_length
#print axioms checked
end Gebendorfer.RadenkovicGutman.IntegerOuterTable
