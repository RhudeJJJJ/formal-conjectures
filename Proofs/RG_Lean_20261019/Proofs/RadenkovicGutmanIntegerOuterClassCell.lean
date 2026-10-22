/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerOuterTerms

namespace Gebendorfer.RadenkovicGutman.IntegerOuterClassCell
open NestedHorner IntegerComputedClassCell
set_option maxHeartbeats 0

noncomputable section
theorem affine_checked (p : NestedHorner.Poly 3) (K : ℚ) (hK : 0 < K)
    (deg : Fin 3 → ℕ) (l w : Fin 3 → ℚ) (raw b a : NestedInteger.Poly 3)
    (hr : LiteralIntegerCell.rawCheck p K raw=true)
    (hrect : NestedInteger.rectangular 3 deg raw=true)
    (hb : b=IntegerAffineStages.inner raw
      (leftNumerator l w) (widthNumerator l w) (denominator l w))
    (ha : a=IntegerOuterTerms.transform (leftNumerator l w 0)
      (widthNumerator l w 0) (denominator l w 0) 0 b) :
    NestedAffine.check 3 p
      (scale (1/(K*(NestedInteger.factor 3 deg (denominator l w) : ℚ)))
        (NestedInteger.castPoly 3 a)) l w=true := by
  apply NestedAffine.check_complete
  intro x
  have he : eval (NestedInteger.castPoly 3 a) x=
      eval (NestedInteger.castPoly 3 (NestedInteger.clearedAll 3 raw
        (leftNumerator l w) (widthNumerator l w) (denominator l w))) x := by
    rw [ha,IntegerOuterTerms.eval_eq_clearedOuter _ _ _
      (PackedIntegerSemanticAffine.denominator_pos l w 0).ne',hb]
    rfl
  have hc := NestedInteger.clearedAll_sound 3 deg raw
    (leftNumerator l w) (widthNumerator l w) (denominator l w)
    hrect (fun i => (PackedIntegerSemanticAffine.denominator_pos l w i).ne') x
  rw [eval_scale,he,hc,LiteralIntegerCell.raw_eval p K raw hr]
  have hv : (fun i => ((leftNumerator l w i : ℝ)+(widthNumerator l w i : ℝ)*x i)/
      (denominator l w i : ℝ))=(fun i => (l i : ℝ)+(w i : ℝ)*x i) := by
    funext i
    exact PackedIntegerSemanticAffine.coordinate_eq l w x i
  rw [hv]
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hF : (0 : ℝ) < NestedInteger.factor 3 deg (denominator l w) := by
    exact_mod_cast NestedInteger.factor_pos 3 deg (denominator l w)
      (PackedIntegerSemanticAffine.denominator_pos l w)
  push_cast
  field_simp

theorem accepts_make {d : ℚ} {c₁ c₂ : Fin 5} {p : NormProgramPack.Pack d c₁ c₂}
    (q : IntegerNormProgramPack.Pack p) (reciprocal : Bool) (s L R : ℚ) (k n : ℕ)
    (deg : Fin 3 → ℕ) (l w : Fin 3 → ℚ) (K A B : ℤ) (raw b a : NestedInteger.Poly 3)
    (hs : 0 < s) (hw : ∀ i, 0 < w i)
    (hK : (K : ℚ)=baseScale s L)
    (hA : (A : ℚ)=(K : ℚ)*(L*(1+s)))
    (hB : (B : ℚ)=(K : ℚ)*(L*(1+1/s)))
    (hr : IntegerNormProgramPack.rawCheck q reciprocal K A B raw=true)
    (hrect : NestedInteger.rectangular 3 deg raw=true)
    (hinner : b=IntegerAffineStages.inner raw
      (leftNumerator l w) (widthNumerator l w) (denominator l w))
    (ha : a=IntegerOuterTerms.transform (leftNumerator l w 0)
      (widthNumerator l w 0) (denominator l w 0) 0 b)
    (hb : NestedInteger.bernsteinCheck 3 deg a=true)
    (hl : RationalLog.accepts L R k n=true) :
    FastNestedCellData.accepts d c₁ c₂
      (LiteralIntegerCell.make p reciprocal s L R k n deg l w a)=true := by
  apply decide_eq_true
  refine ⟨hs,hw,NormProgramPack.accepts_polynomial p reciprocal s L,?_,?_,hl⟩
  · exact affine_checked _ (baseScale s L) (PackedIntegerSemanticAffine.baseScale_pos s L)
      deg l w raw b a
      (IntegerNormProgramPack.raw_checked q reciprocal s L K A B raw hK hA hB hr)
      hrect hinner ha
  · exact NestedPositiveScale.positiveCheck_scale 3 deg _ (1/totalScale s L deg l w)
      (div_nonneg (by norm_num) (PackedIntegerSemanticAffine.totalScale_pos s L deg l w).le)
      (NestedInteger.bernsteinCheck_to_rational 3 deg a hb)

#print axioms affine_checked
#print axioms accepts_make
end
end Gebendorfer.RadenkovicGutman.IntegerOuterClassCell
