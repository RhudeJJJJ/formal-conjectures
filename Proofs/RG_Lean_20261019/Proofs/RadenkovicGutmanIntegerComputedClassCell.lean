/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedClassCell
import Proofs.RadenkovicGutmanNestedPositiveScale
import Proofs.RadenkovicGutmanNestedIntegerAffine

namespace Gebendorfer.RadenkovicGutman.IntegerComputedClassCell
open NestedArithmetic
set_option maxHeartbeats 0

def integerize : (n : ℕ) → ℚ → NestedHorner.Poly n → NestedInteger.Poly n
  | 0,K,p => (K*p).num
  | n+1,K,p => p.map (integerize n K)

def pad : (n : ℕ) → (Fin n → ℕ) → NestedInteger.Poly n → NestedInteger.Poly n
  | 0,_,p => p
  | n+1,d,p => List.ofFn (fun i : Fin (d 0+1) =>
      pad n (fun j => d j.succ) (p.getD i.val (NestedInteger.zero n)))

def denominator (l w : Fin 3 → ℚ) (i : Fin 3) : ℤ := (l i).den*(w i).den
def leftNumerator (l w : Fin 3 → ℚ) (i : Fin 3) : ℤ := (l i).num*(w i).den
def widthNumerator (l w : Fin 3 → ℚ) (i : Fin 3) : ℤ := (w i).num*(l i).den
def baseScale (s L : ℚ) : ℚ := ((L*(1+s)).den : ℚ)*((L*(1+1/s)).den : ℚ)

def integerAffine (d : ℚ) (c₁ c₂ : Fin 5) (reciprocal : Bool) (s L : ℚ)
    (deg : Fin 3 → ℕ) (l w : Fin 3 → ℚ) : NestedInteger.Poly 3 :=
  let p := compile (ComputedClassCell.polynomial d c₁ c₂ reciprocal s L)
  let raw := pad 3 deg (integerize 3 (baseScale s L) p)
  NestedInteger.clearedAll 3 raw (leftNumerator l w) (widthNumerator l w) (denominator l w)

def totalScale (s L : ℚ) (deg : Fin 3 → ℕ) (l w : Fin 3 → ℚ) : ℚ :=
  baseScale s L*(NestedInteger.factor 3 deg (denominator l w) : ℚ)

def make (d : ℚ) (c₁ c₂ : Fin 5) (reciprocal : Bool) (s L R : ℚ) (k n : ℕ)
    (deg : Fin 3 → ℕ) (l w : Fin 3 → ℚ) : FastNestedCellData.Cell :=
  let p := compile (ComputedClassCell.polynomial d c₁ c₂ reciprocal s L)
  let a := integerAffine d c₁ c₂ reciprocal s L deg l w
  { reciprocal := reciprocal
    young := s
    squareLower := L
    payment := R
    logarithmK := k
    logarithmN := n
    poly := p
    affine := NestedHorner.scale (1/totalScale s L deg l w) (NestedInteger.castPoly 3 a)
    degrees := deg
    left := l
    width := w }

/-- Integer signs imply the original rational certificate; exact affine equality
still checks every reconstruction and denominator against the actual program. -/
theorem accepts_make (d : ℚ) (c₁ c₂ : Fin 5) (reciprocal : Bool) (s L R : ℚ) (k n : ℕ)
    (deg : Fin 3 → ℕ) (l w : Fin 3 → ℚ)
    (hK : 0 < totalScale s L deg l w) (hs : 0 < s) (hw : ∀ i, 0 < w i)
    (ha : NestedAffine.check 3 (compile (ComputedClassCell.polynomial d c₁ c₂ reciprocal s L))
      (NestedHorner.scale (1/totalScale s L deg l w)
        (NestedInteger.castPoly 3 (integerAffine d c₁ c₂ reciprocal s L deg l w))) l w=true)
    (hb : NestedInteger.bernsteinCheck 3 deg (integerAffine d c₁ c₂ reciprocal s L deg l w)=true)
    (hl : RationalLog.accepts L R k n=true) :
    FastNestedCellData.accepts d c₁ c₂ (make d c₁ c₂ reciprocal s L R k n deg l w)=true := by
  apply decide_eq_true
  refine ⟨hs,hw,?_,ha,?_,hl⟩
  · unfold NestedArithmetic.accepts
    exact decide_eq_true rfl
  · exact NestedPositiveScale.positiveCheck_scale 3 deg _ (1/totalScale s L deg l w)
      (div_nonneg (by norm_num) hK.le) (NestedInteger.bernsteinCheck_to_rational 3 deg _ hb)

#print axioms accepts_make
end Gebendorfer.RadenkovicGutman.IntegerComputedClassCell
