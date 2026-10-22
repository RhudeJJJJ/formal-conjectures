/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanLiteralIntegerCell

namespace Gebendorfer.RadenkovicGutman.IntegerNormProgramPack
open NestedHorner
set_option maxHeartbeats 0

structure Pack {d : ℚ} {c₁ c₂ : Fin 5} (p : NormProgramPack.Pack d c₁ c₂) where
  u : NestedInteger.Poly 3
  v : NestedInteger.Poly 3
  j : NestedInteger.Poly 3
  ui : NestedInteger.Poly 3
  vi : NestedInteger.Poly 3
  ji : NestedInteger.Poly 3
  hu : NestedInteger.castPoly 3 u=p.u
  hv : NestedInteger.castPoly 3 v=p.v
  hj : NestedInteger.castPoly 3 j=p.j
  hui : NestedInteger.castPoly 3 ui=p.ui
  hvi : NestedInteger.castPoly 3 vi=p.vi
  hji : NestedInteger.castPoly 3 ji=p.ji

def shiftY (k : ℕ) (p : NestedInteger.Poly 3) : NestedInteger.Poly 3 :=
  List.replicate k (NestedInteger.zero 2) ++ p

def zeroCheck : (n : ℕ) → NestedInteger.Poly n → Bool
  | 0,p => decide (p=0)
  | n+1,p => p.all (zeroCheck n)

def polynomial {d : ℚ} {c₁ c₂ : Fin 5} {p : NormProgramPack.Pack d c₁ c₂}
    (q : Pack p) (reciprocal : Bool) (K A B : ℤ) : NestedInteger.Poly 3 :=
  if reciprocal=true then
    let duv := max p.du p.dv
    let D := max p.dj duv
    NestedInteger.add (shiftY (D-p.dj) (NestedInteger.scale K q.ji))
      (shiftY (D-duv) (NestedInteger.add
        (shiftY (duv-p.du) (NestedInteger.scale (-A) q.ui))
        (shiftY (duv-p.dv) (NestedInteger.scale (-B) q.vi))))
  else NestedInteger.add (NestedInteger.scale K q.j)
    (NestedInteger.add (NestedInteger.scale (-A) q.u) (NestedInteger.scale (-B) q.v))

def rawCheck {d : ℚ} {c₁ c₂ : Fin 5} {p : NormProgramPack.Pack d c₁ c₂}
    (q : Pack p) (reciprocal : Bool) (K A B : ℤ) (raw : NestedInteger.Poly 3) : Bool :=
  zeroCheck 3 (NestedInteger.add raw (NestedInteger.scale (-1) (polynomial q reciprocal K A B)))

noncomputable section
theorem eval_shiftY (k : ℕ) (p : NestedInteger.Poly 3) (x : Fin 3 → ℝ) :
    eval (NestedInteger.castPoly 3 (shiftY k p)) x=
      x 0^k*eval (NestedInteger.castPoly 3 p) x := by
  induction k with
  | zero => simp [shiftY]
  | succ k ih =>
    change eval (NestedInteger.castPoly 2 (NestedInteger.zero 2)::
      NestedInteger.castPoly 3 (shiftY k p)) x=_
    rw [eval_cons,NestedInteger.cast_zero,eval_zero,zero_add,ih,pow_succ]
    ring

theorem zeroCheck_sound (n : ℕ) (p : NestedInteger.Poly n)
    (h : zeroCheck n p=true) (x : Fin n → ℝ) : eval (NestedInteger.castPoly n p) x=0 := by
  induction n with
  | zero =>
    have hp : p=0 := of_decide_eq_true h
    subst p
    norm_num [NestedInteger.castPoly,eval]
  | succ n ih =>
    induction p with
    | nil => rfl
    | cons c p hp =>
      have hh : zeroCheck n c=true ∧ zeroCheck (n+1) p=true := by
        simpa only [zeroCheck,List.all_cons,Bool.and_eq_true] using h
      change eval (NestedInteger.castPoly n c::NestedInteger.castPoly (n+1) p) x=0
      rw [eval_cons,ih c hh.1,hp hh.2]
      ring

theorem eval_polynomial {d : ℚ} {c₁ c₂ : Fin 5} {p : NormProgramPack.Pack d c₁ c₂}
    (q : Pack p) (reciprocal : Bool) (s L : ℚ) (K A B : ℤ)
    (hA : (A : ℚ)=(K : ℚ)*(L*(1+s)))
    (hB : (B : ℚ)=(K : ℚ)*(L*(1+1/s))) (x : Fin 3 → ℝ) :
    eval (NestedInteger.castPoly 3 (polynomial q reciprocal K A B)) x=
      (K : ℝ)*eval (NormProgramPack.polynomial p reciprocal s L) x := by
  have hAr : (A : ℝ)=(K : ℝ)*((L : ℝ)*(1+(s : ℝ))) := by exact_mod_cast hA
  have hBr : (B : ℝ)=(K : ℝ)*((L : ℝ)*(1+1/(s : ℝ))) := by exact_mod_cast hB
  by_cases hr : reciprocal=true
  · simp only [polynomial,NormProgramPack.polynomial,if_pos hr,
      NestedInteger.cast_add,eval_add,eval_shiftY,NestedInteger.cast_scale,eval_scale,
      q.hui,q.hvi,q.hji,NestedArithmetic.eval_mul,NestedArithmetic.eval_power,
      NestedArithmetic.eval_coordinate]
    push_cast
    rw [hAr,hBr]
    ring
  · simp only [polynomial,NormProgramPack.polynomial,if_neg hr,
      NestedInteger.cast_add,eval_add,NestedInteger.cast_scale,eval_scale,q.hu,q.hv,q.hj]
    push_cast
    rw [hAr,hBr]
    ring

/-- The rational source identity follows from a pure integer coefficient check
and three scalar equalities. No rational scalar is recomputed per coefficient. -/
theorem raw_checked {d : ℚ} {c₁ c₂ : Fin 5} {p : NormProgramPack.Pack d c₁ c₂}
    (q : Pack p) (reciprocal : Bool) (s L : ℚ) (K A B : ℤ) (raw : NestedInteger.Poly 3)
    (hK : (K : ℚ)=IntegerComputedClassCell.baseScale s L)
    (hA : (A : ℚ)=(K : ℚ)*(L*(1+s)))
    (hB : (B : ℚ)=(K : ℚ)*(L*(1+1/s)))
    (hr : rawCheck q reciprocal K A B raw=true) :
    LiteralIntegerCell.rawCheck (NormProgramPack.polynomial p reciprocal s L)
      (IntegerComputedClassCell.baseScale s L) raw=true := by
  apply NestedAffine.zeroCheck_complete
  intro x
  have hh := zeroCheck_sound 3 _ hr x
  rw [NestedInteger.cast_add,eval_add,NestedInteger.cast_scale,eval_scale,
    eval_polynomial q reciprocal s L K A B hA hB] at hh
  change eval (NestedHorner.add (NestedInteger.castPoly 3 raw)
    (NestedHorner.scale (-IntegerComputedClassCell.baseScale s L)
      (NormProgramPack.polynomial p reciprocal s L))) x=0
  rw [eval_add,eval_scale,← hK]
  push_cast at hh ⊢
  linarith only [hh]

theorem accepts_make {d : ℚ} {c₁ c₂ : Fin 5} {p : NormProgramPack.Pack d c₁ c₂}
    (q : Pack p) (reciprocal : Bool) (s L R : ℚ) (k n : ℕ) (deg : Fin 3 → ℕ)
    (l w : Fin 3 → ℚ) (K A B : ℤ) (raw a : NestedInteger.Poly 3)
    (hs : 0 < s) (hw : ∀ i, 0 < w i)
    (hK : (K : ℚ)=IntegerComputedClassCell.baseScale s L)
    (hA : (A : ℚ)=(K : ℚ)*(L*(1+s)))
    (hB : (B : ℚ)=(K : ℚ)*(L*(1+1/s)))
    (hr : rawCheck q reciprocal K A B raw=true)
    (hrect : NestedInteger.rectangular 3 deg raw=true)
    (ha : a=NestedInteger.clearedAll 3 raw
      (IntegerComputedClassCell.leftNumerator l w) (IntegerComputedClassCell.widthNumerator l w)
      (IntegerComputedClassCell.denominator l w))
    (hb : NestedInteger.bernsteinCheck 3 deg a=true)
    (hl : RationalLog.accepts L R k n=true) :
    FastNestedCellData.accepts d c₁ c₂ (LiteralIntegerCell.make p reciprocal s L R k n deg l w a)=true :=
  LiteralIntegerCell.accepts_make p reciprocal s L R k n deg l w raw a hs hw
    (raw_checked q reciprocal s L K A B raw hK hA hB hr) hrect ha hb hl

#print axioms eval_polynomial
#print axioms raw_checked
#print axioms accepts_make
end
end Gebendorfer.RadenkovicGutman.IntegerNormProgramPack
