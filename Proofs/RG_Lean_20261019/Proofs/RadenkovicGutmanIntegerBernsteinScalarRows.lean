/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerPolynomialPaymentCell
import Proofs.RadenkovicGutmanIntegerBernsteinTable

namespace Gebendorfer.RadenkovicGutman.IntegerBernsteinScalarRows

/-- Checked scalar rows prove the existing one-dimensional checker. -/
theorem checked (p : List ℤ) (N : ℕ) (hN : p.length = N)
    (rows : Fin (N+1) → ℤ)
    (hr : ∀ j, rows j = NestedInteger.coefficientFrom N j.val 0 p)
    (hs : ∀ j, 0 ≤ rows j) : IntegerPolynomialPaymentCell.positive p = true := by
  have hbern : NestedInteger.bernsteinCheck 1 (fun _ => N) p = true :=
    IntegerBernsteinRows.checked (n := 0) (fun _ => N) p rows
      (by calc p.length = N := hN; _ ≤ N+1 := Nat.le_succ N)
      hr (fun j => decide_eq_true (hs j))
  simp only [IntegerPolynomialPaymentCell.positive, NestedInteger.accepts, hN,
    hbern, Bool.or_true]

#print axioms checked
end Gebendorfer.RadenkovicGutman.IntegerBernsteinScalarRows
