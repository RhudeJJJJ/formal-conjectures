/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanPackedIntegerClassCell
import Proofs.RadenkovicGutmanNestedAffineComplete

namespace Gebendorfer.RadenkovicGutman.PackedIntegerSemanticAffine
open IntegerComputedClassCell NestedHorner
noncomputable section
set_option maxHeartbeats 0

theorem pad_rectangular (n : ℕ) (deg : Fin n → ℕ) (p : NestedInteger.Poly n) :
    NestedInteger.rectangular n deg (pad n deg p)=true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [pad,NestedInteger.rectangular,List.length_ofFn,decide_true,Bool.true_and]
    apply List.all_eq_true.mpr
    intro c hc
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hc
    exact ih _ _

theorem denominator_pos (l w : Fin 3 → ℚ) (i : Fin 3) : 0 < denominator l w i := by
  unfold denominator
  exact mul_pos (by exact_mod_cast (l i).den_pos) (by exact_mod_cast (w i).den_pos)

theorem coordinate_eq (l w : Fin 3 → ℚ) (x : Fin 3 → ℝ) (i : Fin 3) :
    ((leftNumerator l w i : ℝ)+(widthNumerator l w i : ℝ)*x i)/
      (denominator l w i : ℝ) = (l i : ℝ)+(w i : ℝ)*x i := by
  have hl : (0 : ℝ) < (l i).den := by exact_mod_cast (l i).den_pos
  have hw : (0 : ℝ) < (w i).den := by exact_mod_cast (w i).den_pos
  unfold leftNumerator widthNumerator denominator
  push_cast
  rw [Rat.cast_def,Rat.cast_def]
  field_simp

def raw (p : NestedHorner.Poly 3) (K : ℚ) (deg : Fin 3 → ℕ) : NestedInteger.Poly 3 :=
  pad 3 deg (integerize 3 K p)

def rawCheck (p : NestedHorner.Poly 3) (K : ℚ) (deg : Fin 3 → ℕ) : Bool :=
  NestedAffine.zeroCheck 3 (add (NestedInteger.castPoly 3 (raw p K deg)) (scale (-K) p))

theorem raw_eval (p : NestedHorner.Poly 3) (K : ℚ) (deg : Fin 3 → ℕ)
    (h : rawCheck p K deg=true) (z : Fin 3 → ℝ) :
    eval (NestedInteger.castPoly 3 (raw p K deg)) z=(K : ℝ)*eval p z := by
  have hh := NestedAffine.zeroCheck_sound 3 _ h z
  rw [eval_add,eval_scale] at hh
  push_cast at hh
  linarith only [hh]

theorem affine_checked (p : NestedHorner.Poly 3) (K : ℚ) (hK : 0 < K)
    (deg : Fin 3 → ℕ) (l w : Fin 3 → ℚ) (hr : rawCheck p K deg=true) :
    NestedAffine.check 3 p
      (scale (1/(K*(NestedInteger.factor 3 deg (denominator l w) : ℚ)))
        (NestedInteger.castPoly 3 (NestedInteger.clearedAll 3 (raw p K deg)
          (leftNumerator l w) (widthNumerator l w) (denominator l w)))) l w=true := by
  apply NestedAffine.check_complete
  intro x
  have he := NestedInteger.clearedAll_sound 3 deg (raw p K deg)
    (leftNumerator l w) (widthNumerator l w) (denominator l w)
    (pad_rectangular 3 deg _) (fun i => (denominator_pos l w i).ne') x
  rw [eval_scale,he,raw_eval p K deg hr]
  have hv : (fun i => ((leftNumerator l w i : ℝ)+(widthNumerator l w i : ℝ)*x i)/
      (denominator l w i : ℝ)) = (fun i => (l i : ℝ)+(w i : ℝ)*x i) := by
    funext i
    exact coordinate_eq l w x i
  rw [hv]
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hF : (0 : ℝ) < NestedInteger.factor 3 deg (denominator l w) := by
    exact_mod_cast NestedInteger.factor_pos 3 deg (denominator l w) (denominator_pos l w)
  push_cast
  field_simp

theorem baseScale_pos (s L : ℚ) : 0 < baseScale s L := by
  unfold baseScale
  exact mul_pos (by exact_mod_cast (L*(1+s)).den_pos)
    (by exact_mod_cast (L*(1+1/s)).den_pos)

theorem totalScale_pos (s L : ℚ) (deg : Fin 3 → ℕ) (l w : Fin 3 → ℚ) :
    0 < totalScale s L deg l w := by
  unfold totalScale
  exact mul_pos (baseScale_pos s L) (by
    exact_mod_cast NestedInteger.factor_pos 3 deg (denominator l w) (denominator_pos l w))

/-- Only the untransformed denominator clearing and integer Bernstein signs are
computed per leaf. The full affine identity follows from the proved transform. -/
theorem accepts_make {d : ℚ} {c₁ c₂ : Fin 5} (p : NormProgramPack.Pack d c₁ c₂)
    (reciprocal : Bool) (s L R : ℚ) (k n : ℕ) (deg : Fin 3 → ℕ) (l w : Fin 3 → ℚ)
    (hs : 0 < s) (hw : ∀ i, 0 < w i)
    (hr : rawCheck (NormProgramPack.polynomial p reciprocal s L) (baseScale s L) deg=true)
    (hb : NestedInteger.bernsteinCheck 3 deg
      (PackedIntegerClassCell.integerAffine p reciprocal s L deg l w)=true)
    (hl : RationalLog.accepts L R k n=true) :
    FastNestedCellData.accepts d c₁ c₂
      (PackedIntegerClassCell.make p reciprocal s L R k n deg l w)=true := by
  apply PackedIntegerClassCell.accepts_make p reciprocal s L R k n deg l w
    (totalScale_pos s L deg l w) hs hw _ hb hl
  exact affine_checked _ (baseScale s L) (baseScale_pos s L) deg l w hr

#print axioms affine_checked
#print axioms accepts_make
end
end Gebendorfer.RadenkovicGutman.PackedIntegerSemanticAffine
