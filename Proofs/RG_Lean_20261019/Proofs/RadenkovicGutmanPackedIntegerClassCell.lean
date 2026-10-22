/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerComputedClassCell
import Proofs.RadenkovicGutmanNormProgramPack

namespace Gebendorfer.RadenkovicGutman.PackedIntegerClassCell
open IntegerComputedClassCell
set_option maxHeartbeats 0

def integerAffine {d : ℚ} {c₁ c₂ : Fin 5} (p : NormProgramPack.Pack d c₁ c₂)
    (reciprocal : Bool) (s L : ℚ) (deg : Fin 3 → ℕ) (l w : Fin 3 → ℚ) : NestedInteger.Poly 3 :=
  let raw := pad 3 deg (integerize 3 (baseScale s L) (NormProgramPack.polynomial p reciprocal s L))
  NestedInteger.clearedAll 3 raw (leftNumerator l w) (widthNumerator l w) (denominator l w)

def make {d : ℚ} {c₁ c₂ : Fin 5} (p : NormProgramPack.Pack d c₁ c₂)
    (reciprocal : Bool) (s L R : ℚ) (k n : ℕ)
    (deg : Fin 3 → ℕ) (l w : Fin 3 → ℚ) : FastNestedCellData.Cell :=
  let a := integerAffine p reciprocal s L deg l w
  { reciprocal := reciprocal
    young := s
    squareLower := L
    payment := R
    logarithmK := k
    logarithmN := n
    poly := NormProgramPack.polynomial p reciprocal s L
    affine := NestedHorner.scale (1/totalScale s L deg l w) (NestedInteger.castPoly 3 a)
    degrees := deg
    left := l
    width := w }

/-- Reuse the six closed normal-form proofs. Every leaf still checks its exact
affine reconstruction, denominator clearing, integer Bernstein signs and log. -/
theorem accepts_make {d : ℚ} {c₁ c₂ : Fin 5} (p : NormProgramPack.Pack d c₁ c₂)
    (reciprocal : Bool) (s L R : ℚ) (k n : ℕ) (deg : Fin 3 → ℕ) (l w : Fin 3 → ℚ)
    (hK : 0 < totalScale s L deg l w) (hs : 0 < s) (hw : ∀ i, 0 < w i)
    (ha : NestedAffine.check 3 (NormProgramPack.polynomial p reciprocal s L)
      (NestedHorner.scale (1/totalScale s L deg l w)
        (NestedInteger.castPoly 3 (integerAffine p reciprocal s L deg l w))) l w=true)
    (hb : NestedInteger.bernsteinCheck 3 deg (integerAffine p reciprocal s L deg l w)=true)
    (hl : RationalLog.accepts L R k n=true) :
    FastNestedCellData.accepts d c₁ c₂ (make p reciprocal s L R k n deg l w)=true := by
  apply decide_eq_true
  refine ⟨hs,hw,?_,ha,?_,hl⟩
  · exact NormProgramPack.accepts_polynomial p reciprocal s L
  · exact NestedPositiveScale.positiveCheck_scale 3 deg _ (1/totalScale s L deg l w)
      (div_nonneg (by norm_num) hK.le) (NestedInteger.bernsteinCheck_to_rational 3 deg _ hb)

#print axioms accepts_make
end Gebendorfer.RadenkovicGutman.PackedIntegerClassCell
