/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFastNestedCellData

namespace Gebendorfer.RadenkovicGutman.ComputedClassCell
open NestedHorner NestedArithmetic
set_option maxHeartbeats 0

theorem zeroCheck_neg_self (n : ℕ) (p : Poly n) :
    NestedAffine.zeroCheck n (add p (scale (-1) p))=true := by
  induction n with
  | zero => simp [NestedAffine.zeroCheck,add,scale]
  | succ n ih =>
    induction p with
    | nil => rfl
    | cons c p hp =>
      simp only [add,scale,List.map_cons,zipAdd,NestedAffine.zeroCheck,List.all_cons]
      simp only [ih,Bool.true_and]
      exact hp

def polynomial (d : ℚ) (c₁ c₂ : Fin 5) (reciprocal : Bool) (s L : ℚ) : Expr 3 :=
  if reciprocal=true then (NestedReciprocal.homogenize (NestedClassCell.gap d c₁ c₂ s L)).2
  else NestedClassCell.gap d c₁ c₂ s L

/-- Only rational scalar data are stored. The kernel reconstructs both polynomials. -/
def make (d : ℚ) (c₁ c₂ : Fin 5) (reciprocal : Bool) (s L R : ℚ) (k n : ℕ)
    (deg : Fin 3 → ℕ) (l w : Fin 3 → ℚ) : FastNestedCellData.Cell :=
  let p := compile (polynomial d c₁ c₂ reciprocal s L)
  { reciprocal := reciprocal
    young := s
    squareLower := L
    payment := R
    logarithmK := k
    logarithmN := n
    poly := p
    affine := NestedAffine.transform 3 p l w
    degrees := deg
    left := l
    width := w }

theorem accepts_make (d : ℚ) (c₁ c₂ : Fin 5) (reciprocal : Bool) (s L R : ℚ) (k n : ℕ)
    (deg : Fin 3 → ℕ) (l w : Fin 3 → ℚ) (hs : 0 < s) (hw : ∀ i, 0 < w i)
    (hpositive : positiveCheck 3 deg
      (NestedAffine.transform 3 (compile (polynomial d c₁ c₂ reciprocal s L)) l w)=true)
    (hlog : RationalLog.accepts L R k n=true) :
    FastNestedCellData.accepts d c₁ c₂ (make d c₁ c₂ reciprocal s L R k n deg l w)=true := by
  apply decide_eq_true
  refine ⟨hs,hw,?_,?_,hpositive,hlog⟩
  · unfold NestedArithmetic.accepts
    exact decide_eq_true rfl
  · exact zeroCheck_neg_self 3 _

#print axioms zeroCheck_neg_self
#print axioms accepts_make
end Gebendorfer.RadenkovicGutman.ComputedClassCell
