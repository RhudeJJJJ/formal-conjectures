/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerDataElaboration

namespace Gebendorfer.RadenkovicGutman.LiteralIntegerCell
open IntegerComputedClassCell NestedHorner
set_option maxHeartbeats 0

def rawCheck (p : NestedHorner.Poly 3) (K : ℚ) (raw : NestedInteger.Poly 3) : Bool :=
  NestedAffine.zeroCheck 3 (add (NestedInteger.castPoly 3 raw) (scale (-K) p))

def make {d : ℚ} {c₁ c₂ : Fin 5} (p : NormProgramPack.Pack d c₁ c₂)
    (reciprocal : Bool) (s L R : ℚ) (k n : ℕ) (deg : Fin 3 → ℕ) (l w : Fin 3 → ℚ)
    (a : NestedInteger.Poly 3) : FastNestedCellData.Cell :=
  { reciprocal := reciprocal
    young := s
    squareLower := L
    payment := R
    logarithmK := k
    logarithmN := n
    poly := NormProgramPack.polynomial p reciprocal s L
    affine := scale (1/totalScale s L deg l w) (NestedInteger.castPoly 3 a)
    degrees := deg
    left := l
    width := w }

noncomputable section
theorem raw_eval (p : NestedHorner.Poly 3) (K : ℚ) (raw : NestedInteger.Poly 3)
    (h : rawCheck p K raw=true) (z : Fin 3 → ℝ) :
    eval (NestedInteger.castPoly 3 raw) z=(K : ℝ)*eval p z := by
  have hh := NestedAffine.zeroCheck_sound 3 _ h z
  rw [eval_add,eval_scale] at hh
  push_cast at hh
  linarith only [hh]

theorem affine_checked (p : NestedHorner.Poly 3) (K : ℚ) (hK : 0 < K)
    (deg : Fin 3 → ℕ) (l w : Fin 3 → ℚ) (raw a : NestedInteger.Poly 3)
    (hr : rawCheck p K raw=true) (hrect : NestedInteger.rectangular 3 deg raw=true)
    (ha : a=NestedInteger.clearedAll 3 raw
      (leftNumerator l w) (widthNumerator l w) (denominator l w)) :
    NestedAffine.check 3 p
      (scale (1/(K*(NestedInteger.factor 3 deg (denominator l w) : ℚ)))
        (NestedInteger.castPoly 3 a)) l w=true := by
  apply NestedAffine.check_complete
  intro x
  have he := NestedInteger.clearedAll_sound 3 deg raw
    (leftNumerator l w) (widthNumerator l w) (denominator l w)
    hrect (fun i => (PackedIntegerSemanticAffine.denominator_pos l w i).ne') x
  rw [eval_scale,ha,he,raw_eval p K raw hr]
  have hv : (fun i => ((leftNumerator l w i : ℝ)+(widthNumerator l w i : ℝ)*x i)/
      (denominator l w i : ℝ)) = (fun i => (l i : ℝ)+(w i : ℝ)*x i) := by
    funext i
    exact PackedIntegerSemanticAffine.coordinate_eq l w x i
  rw [hv]
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hF : (0 : ℝ) < NestedInteger.factor 3 deg (denominator l w) := by
    exact_mod_cast NestedInteger.factor_pos 3 deg (denominator l w)
      (PackedIntegerSemanticAffine.denominator_pos l w)
  push_cast
  field_simp

/-- The raw program identity and the integer transform identity are checked
separately. Thus neither identity repeatedly reconstructs the other tensor. -/
theorem accepts_make {d : ℚ} {c₁ c₂ : Fin 5} (p : NormProgramPack.Pack d c₁ c₂)
    (reciprocal : Bool) (s L R : ℚ) (k n : ℕ) (deg : Fin 3 → ℕ) (l w : Fin 3 → ℚ)
    (raw a : NestedInteger.Poly 3) (hs : 0 < s) (hw : ∀ i, 0 < w i)
    (hr : rawCheck (NormProgramPack.polynomial p reciprocal s L) (baseScale s L) raw=true)
    (hrect : NestedInteger.rectangular 3 deg raw=true)
    (ha : a=NestedInteger.clearedAll 3 raw
      (leftNumerator l w) (widthNumerator l w) (denominator l w))
    (hb : NestedInteger.bernsteinCheck 3 deg a=true)
    (hl : RationalLog.accepts L R k n=true) :
    FastNestedCellData.accepts d c₁ c₂ (make p reciprocal s L R k n deg l w a)=true := by
  apply decide_eq_true
  refine ⟨hs,hw,NormProgramPack.accepts_polynomial p reciprocal s L,?_,?_,hl⟩
  · exact affine_checked _ (baseScale s L) (PackedIntegerSemanticAffine.baseScale_pos s L)
      deg l w raw a hr hrect ha
  · exact NestedPositiveScale.positiveCheck_scale 3 deg _ (1/totalScale s L deg l w)
      (div_nonneg (by norm_num) (PackedIntegerSemanticAffine.totalScale_pos s L deg l w).le)
      (NestedInteger.bernsteinCheck_to_rational 3 deg a hb)

#print axioms affine_checked
#print axioms accepts_make
end
end Gebendorfer.RadenkovicGutman.LiteralIntegerCell
