/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerBernsteinRows

namespace Gebendorfer.RadenkovicGutman.IntegerWeightedBernstein
open NestedInteger
set_option maxHeartbeats 0

/-- `none` preserves the exact zero-polynomial branch of the original checker.
Each remaining scalar weight is checked once for the entire coefficient row. -/
def weights {n : ℕ} (D j : ℕ) : ℕ → Poly (n+1) → List (Option ℤ)
  | _,[] => []
  | k,_::p => (if k ≤ j then some (Nat.fast_choose (D-k) (j-k) : ℤ) else none) ::
      weights D j (k+1) p

def applyWeights {n : ℕ} : List (Option ℤ) → Poly (n+1) → Poly n
  | _,[] => zero n
  | [],_::_ => zero n
  | v::rows,c::p => add (match v with | none => zero n | some v => scale v c)
      (applyWeights rows p)

theorem apply_source {n : ℕ} (D j k : ℕ) (p : Poly (n+1)) :
    applyWeights (weights D j k p) p=coefficientFrom D j k p := by
  induction p generalizing k with
  | nil => rfl
  | cons c p ih =>
    by_cases h : k ≤ j
    · simp only [weights,if_pos h,applyWeights,coefficientFrom,ih]
    · simp only [weights,if_neg h,applyWeights,coefficientFrom,ih]

theorem checked {n : ℕ} (D j k : ℕ) (p : Poly (n+1)) (a : Poly n)
    (rows : List (Option ℤ)) (hw : rows=weights D j k p)
    (ha : a=applyWeights rows p) : a=coefficientFrom D j k p := by
  rw [ha,hw,apply_source]

#print axioms apply_source
#print axioms checked
end Gebendorfer.RadenkovicGutman.IntegerWeightedBernstein
