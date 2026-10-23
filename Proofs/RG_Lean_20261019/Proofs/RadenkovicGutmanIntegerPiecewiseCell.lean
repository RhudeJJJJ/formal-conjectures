/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerScaledCell
import Proofs.RadenkovicGutmanIntegerOuterPieces

namespace Gebendorfer.RadenkovicGutman.IntegerPiecewiseCell
open NestedHorner
set_option maxHeartbeats 0
noncomputable section

theorem affine_checked (p : NestedHorner.Poly 3) (K : ℤ) (hK : 0 < K)
    (deg : Fin 3 → ℕ) (l w : Fin 3 → ℚ) (lN wN D : Fin 3 → ℤ)
    (raw b a : NestedInteger.Poly 3)
    (hD : ∀ i, 0 < D i)
    (hcoord : ∀ i, (lN i : ℚ)/(D i : ℚ)=l i ∧ (wN i : ℚ)/(D i : ℚ)=w i)
    (hr : ∀ x, eval (NestedInteger.castPoly 3 raw) x=(K : ℝ)*eval p x)
    (hrect : NestedInteger.rectangular 3 deg raw=true)
    (hb : b=IntegerAffineStages.inner raw lN wN D)
    (ha : ∀ x, eval (NestedInteger.castPoly 3 a) x=
      eval (NestedInteger.castPoly 3 (IntegerOuterTerms.transform (lN 0) (wN 0) (D 0) 0 b)) x) :
    NestedAffine.check 3 p (scale (1/IntegerScaledCell.totalScale K deg D)
      (NestedInteger.castPoly 3 a)) l w=true := by
  have h := IntegerScaledCell.affine_checked p K hK deg l w lN wN D raw b
    (IntegerOuterTerms.transform (lN 0) (wN 0) (D 0) 0 b)
    hD hcoord hr hrect hb rfl
  apply NestedAffine.check_complete
  intro x
  rw [eval_scale,ha x]
  simpa only [eval_scale] using NestedAffine.check_sound 3 _ _ l w h x

/-- The same cell checker accepts an exact semantic outer identity assembled
from checked pieces. All scalar, coordinate and sign checks are retained. -/
theorem accepts_make {d : ℚ} {c₁ c₂ : Fin 5} {p : NormProgramPack.Pack d c₁ c₂}
    (q : IntegerNormProgramPack.Pack p) (reciprocal : Bool) (s L R : ℚ) (k n : ℕ)
    (deg : Fin 3 → ℕ) (l w : Fin 3 → ℚ) (K A B : ℤ) (lN wN D : Fin 3 → ℤ)
    (raw b a : NestedInteger.Poly 3) (hK : 0 < K) (hs : 0 < s) (hw : ∀ i, 0 < w i)
    (hA : (A : ℚ)=(K : ℚ)*(L*(1+s)))
    (hB : (B : ℚ)=(K : ℚ)*(L*(1+1/s)))
    (hD : ∀ i, 0 < D i)
    (hcoord : ∀ i, (lN i : ℚ)/(D i : ℚ)=l i ∧ (wN i : ℚ)/(D i : ℚ)=w i)
    (hr : IntegerNormProgramPack.rawCheck q reciprocal K A B raw=true)
    (hrect : NestedInteger.rectangular 3 deg raw=true)
    (hinner : b=IntegerAffineStages.inner raw lN wN D)
    (ha : ∀ x, eval (NestedInteger.castPoly 3 a) x=
      eval (NestedInteger.castPoly 3 (IntegerOuterTerms.transform (lN 0) (wN 0) (D 0) 0 b)) x)
    (hb : NestedInteger.bernsteinCheck 3 deg a=true)
    (hl : RationalLog.accepts L R k n=true) :
    FastNestedCellData.accepts d c₁ c₂
      (IntegerScaledCell.make p reciprocal s L R k n deg l w K D a)=true := by
  apply decide_eq_true
  refine ⟨hs,hw,NormProgramPack.accepts_polynomial p reciprocal s L,?_,?_,hl⟩
  · exact affine_checked _ K hK deg l w lN wN D raw b a hD hcoord
      (IntegerScaledCell.raw_eval q reciprocal s L K A B raw hA hB hr) hrect hinner ha
  · have hscale : (0 : ℚ) < IntegerScaledCell.totalScale K deg D := by
      exact mul_pos (by exact_mod_cast hK)
        (by exact_mod_cast NestedInteger.factor_pos 3 deg D hD)
    exact NestedPositiveScale.positiveCheck_scale 3 deg _
      (1/IntegerScaledCell.totalScale K deg D) (div_nonneg (by norm_num) hscale.le)
      (NestedInteger.bernsteinCheck_to_rational 3 deg a hb)

#print axioms affine_checked
#print axioms accepts_make
end
end Gebendorfer.RadenkovicGutman.IntegerPiecewiseCell
