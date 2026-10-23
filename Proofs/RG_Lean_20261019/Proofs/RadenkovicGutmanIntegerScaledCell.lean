/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerOuterTerms

namespace Gebendorfer.RadenkovicGutman.IntegerScaledCell
open NestedHorner
set_option maxHeartbeats 0

def totalScale (K : ℤ) (deg : Fin 3 → ℕ) (D : Fin 3 → ℤ) : ℚ :=
  (K : ℚ)*(NestedInteger.factor 3 deg D : ℚ)

def make {d : ℚ} {c₁ c₂ : Fin 5} (p : NormProgramPack.Pack d c₁ c₂)
    (reciprocal : Bool) (s L R : ℚ) (k n : ℕ) (deg : Fin 3 → ℕ)
    (l w : Fin 3 → ℚ) (K : ℤ) (D : Fin 3 → ℤ) (a : NestedInteger.Poly 3) :
    FastNestedCellData.Cell :=
  { reciprocal := reciprocal
    young := s
    squareLower := L
    payment := R
    logarithmK := k
    logarithmN := n
    poly := NormProgramPack.polynomial p reciprocal s L
    affine := scale (1/totalScale K deg D) (NestedInteger.castPoly 3 a)
    degrees := deg
    left := l
    width := w }

noncomputable section
theorem raw_eval {d : ℚ} {c₁ c₂ : Fin 5} {p : NormProgramPack.Pack d c₁ c₂}
    (q : IntegerNormProgramPack.Pack p) (reciprocal : Bool) (s L : ℚ)
    (K A B : ℤ) (raw : NestedInteger.Poly 3)
    (hA : (A : ℚ)=(K : ℚ)*(L*(1+s)))
    (hB : (B : ℚ)=(K : ℚ)*(L*(1+1/s)))
    (hr : IntegerNormProgramPack.rawCheck q reciprocal K A B raw=true)
    (x : Fin 3 → ℝ) :
    eval (NestedInteger.castPoly 3 raw) x=
      (K : ℝ)*eval (NormProgramPack.polynomial p reciprocal s L) x := by
  have hh := IntegerNormProgramPack.zeroCheck_sound 3 _ hr x
  rw [NestedInteger.cast_add,eval_add,NestedInteger.cast_scale,eval_scale,
    IntegerNormProgramPack.eval_polynomial q reciprocal s L K A B hA hB] at hh
  push_cast at hh
  linarith only [hh]

theorem affine_checked (p : NestedHorner.Poly 3) (K : ℤ) (hK : 0 < K)
    (deg : Fin 3 → ℕ) (l w : Fin 3 → ℚ) (lN wN D : Fin 3 → ℤ)
    (raw b a : NestedInteger.Poly 3)
    (hD : ∀ i, 0 < D i)
    (hcoord : ∀ i, (lN i : ℚ)/(D i : ℚ)=l i ∧ (wN i : ℚ)/(D i : ℚ)=w i)
    (hr : ∀ x, eval (NestedInteger.castPoly 3 raw) x=(K : ℝ)*eval p x)
    (hrect : NestedInteger.rectangular 3 deg raw=true)
    (hb : b=IntegerAffineStages.inner raw lN wN D)
    (ha : a=IntegerOuterTerms.transform (lN 0) (wN 0) (D 0) 0 b) :
    NestedAffine.check 3 p (scale (1/totalScale K deg D) (NestedInteger.castPoly 3 a)) l w=true := by
  apply NestedAffine.check_complete
  intro x
  have he : eval (NestedInteger.castPoly 3 a) x=
      eval (NestedInteger.castPoly 3 (NestedInteger.clearedAll 3 raw lN wN D)) x := by
    rw [ha,IntegerOuterTerms.eval_eq_clearedOuter _ _ _ (hD 0).ne',hb]
    rfl
  have hc := NestedInteger.clearedAll_sound 3 deg raw lN wN D hrect (fun i => (hD i).ne') x
  rw [eval_scale,he,hc,hr]
  have hv : (fun i => ((lN i : ℝ)+(wN i : ℝ)*x i)/(D i : ℝ))=
      (fun i => (l i : ℝ)+(w i : ℝ)*x i) := by
    funext i
    have hl : (lN i : ℝ)/(D i : ℝ)=(l i : ℝ) := by exact_mod_cast (hcoord i).1
    have hw : (wN i : ℝ)/(D i : ℝ)=(w i : ℝ) := by exact_mod_cast (hcoord i).2
    calc
      _ = (lN i : ℝ)/(D i : ℝ)+((wN i : ℝ)/(D i : ℝ))*x i := by ring
      _ = _ := by rw [hl,hw]
  rw [hv]
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hF : (0 : ℝ) < NestedInteger.factor 3 deg D := by
    exact_mod_cast NestedInteger.factor_pos 3 deg D hD
  dsimp [totalScale]
  push_cast
  field_simp

/-- Arbitrary positive integer clearing is valid when its two scalar weights
and the three affine coordinates are checked exactly. Least common multiples
can therefore replace unreduced denominator products without changing a bound. -/
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
    (ha : a=IntegerOuterTerms.transform (lN 0) (wN 0) (D 0) 0 b)
    (hb : NestedInteger.bernsteinCheck 3 deg a=true)
    (hl : RationalLog.accepts L R k n=true) :
    FastNestedCellData.accepts d c₁ c₂ (make p reciprocal s L R k n deg l w K D a)=true := by
  apply decide_eq_true
  refine ⟨hs,hw,NormProgramPack.accepts_polynomial p reciprocal s L,?_,?_,hl⟩
  · exact affine_checked _ K hK deg l w lN wN D raw b a hD hcoord
      (raw_eval q reciprocal s L K A B raw hA hB hr) hrect hinner ha
  · have hscale : (0 : ℚ) < totalScale K deg D := by
      exact mul_pos (by exact_mod_cast hK)
        (by exact_mod_cast NestedInteger.factor_pos 3 deg D hD)
    exact NestedPositiveScale.positiveCheck_scale 3 deg _ (1/totalScale K deg D)
      (div_nonneg (by norm_num) hscale.le)
      (NestedInteger.bernsteinCheck_to_rational 3 deg a hb)

#print axioms raw_eval
#print axioms affine_checked
#print axioms accepts_make
end
end Gebendorfer.RadenkovicGutman.IntegerScaledCell
