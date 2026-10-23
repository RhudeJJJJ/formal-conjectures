/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerOuterTerms

namespace Gebendorfer.RadenkovicGutman.IntegerWeightedOuter
open NestedInteger
set_option maxHeartbeats 0

/-- Scalar binomial weights can be checked once and reused for all coefficients
of the lower-dimensional polynomial. They remain exact integer data. -/
def weights {n : ℕ} (l w D : ℤ) : ℕ → Poly (n+1) → List (List ℤ)
  | _,[] => []
  | k,_::p => List.ofFn (fun j : Fin (k+1) =>
      D^p.length*(Nat.fast_choose k j.val : ℤ)*l^(k-j.val)*w^j.val) ::
      weights l w D (k+1) p

def applyWeights {n : ℕ} : List (List ℤ) → Poly (n+1) → Poly (n+1)
  | _,[] => []
  | [],_::_ => []
  | row::rows,c::p => add (row.map (fun v => scale v c)) (applyWeights rows p)

theorem apply_source {n : ℕ} (l w D : ℤ) (k : ℕ) (p : Poly (n+1)) :
    applyWeights (weights l w D k p) p=IntegerOuterTerms.transform l w D k p := by
  induction p generalizing k with
  | nil => rfl
  | cons c p ih =>
    simp only [weights,applyWeights,IntegerOuterTerms.transform,IntegerOuterTerms.term,List.map_ofFn]
    rw [ih]
    rfl

theorem checked {n : ℕ} (l w D : ℤ) (k : ℕ) (p a : Poly (n+1))
    (rows : List (List ℤ)) (hw : rows=weights l w D k p)
    (ha : a=applyWeights rows p) : a=IntegerOuterTerms.transform l w D k p := by
  rw [ha,hw,apply_source]

#print axioms apply_source
#print axioms checked
end Gebendorfer.RadenkovicGutman.IntegerWeightedOuter
