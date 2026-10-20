/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanTailHalfCertificate
import Proofs.RadenkovicGutmanTailHalfGeometry

/-! Original actual-graph half-tail for all d>=46 and y>=1/2.
The same core, root, Schur disk and physical arms are retained. -/
namespace Gebendorfer.RadenkovicGutman.HighDegreeTail
open Focus CoreQuotient TailHalfPolynomial TailHalfGeometry TailHalfCertificate Set
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

theorem x_rescale (y a b : ℝ) (hy : 0 < y) :
    xForm (1/y) a b = (1/y)^8*xCoeff y (y+a/y) (y+b/y) := by
  simp [xForm,aa,bb,ar,ai,nr,ni,br,bi,dr,di,xCoeff,A,B,N₀,D₀,z,
    Complex.normSq_apply,Complex.star_def]
  field_simp [hy.ne']
  ring

theorem t_rescale (y a b : ℝ) (hy : 0 < y) :
    tForm (1/y) a b = (1/y)^7*tCoeff y (y+a/y) (y+b/y) := by
  simp [tForm,aa,bb,ar,ai,nr,ni,br,bi,dr,di,tCoeff,A,B,N₀,D₀,z,
    Complex.normSq_apply,Complex.star_def]
  field_simp [hy.ne']
  ring

theorem c_rescale (y a b : ℝ) (hy : 0 < y) :
    cForm (1/y) a b = (1/y)^8*cCoeff y (y+a/y) (y+b/y) := by
  simp [cForm,aa,bb,ar,ai,nr,ni,br,bi,dr,di,cCoeff,A,B,N₀,D₀,z,
    Complex.normSq_apply]
  field_simp [hy.ne']
  ring

theorem v_rescale (d y a b : ℝ) (hd : 0 < d) (hy : 0 < y) :
    vForm (1/d) (1/y) a b = (1/d)*(1/y)^8*centerValue d y (y+a/y) (y+b/y) := by
  unfold vForm
  rw [x_rescale y a b hy,t_rescale y a b hy,c_rescale y a b hy]
  unfold centerValue
  field_simp [hd.ne',hy.ne']
  ring

theorem k_rescale (d y a b : ℝ) (hd : 0 < d) (hy : 0 < y) :
    kForm (1/d) (1/y) a b = ((1/d)*(1/y)^8)^2*squareMargin d y (y+a/y) (y+b/y) := by
  unfold kForm squareMargin
  rw [v_rescale d y a b hd hy,x_rescale y a b hy,t_rescale y a b hy]
  unfold r
  field_simp [hd.ne',hy.ne']
  ring

theorem log_lower (d y a b : ℝ) (hd : 46 ≤ d) (hy : (1/2 : ℝ) ≤ y)
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1)
    (ζ : ℂ) (hζ : ‖ζ-g d y‖ ≤ r d y) :
    TailIntegral.phi y ≤ Real.log ‖quotient y (y+a/y) (y+b/y) ζ‖ := by
  have hd0 : 0 < d := by linarith
  have hy0 : 0 < y := by linarith
  have hh : 1/d ∈ Icc (0 : ℝ) (1/46) := by
    refine ⟨by positivity,?_⟩
    apply (div_le_div_iff₀ hd0 (by norm_num : (0 : ℝ) < 46)).mpr
    linarith
  have hu : 1/y ∈ Icc (0 : ℝ) 2 := by
    refine ⟨by positivity,(div_le_iff₀ hy0).mpr ?_⟩
    linarith
  have hv := v_nonneg (1/d) (1/y) a b hh hu ha hb
  have hk := k_nonneg (1/d) (1/y) a b hh hu ha hb
  rw [v_rescale d y a b hd0 hy0] at hv
  rw [k_rescale d y a b hd0 hy0] at hk
  have hs : 0 < (1/d)*(1/y)^8 := by positivity
  apply log_lower_of_margins d y (y+a/y) (y+b/y) hd0.le hy0
    (by have h := div_nonneg ha.1 hy0.le; linarith)
    (by have h := div_nonneg hb.1 hy0.le; linarith)
    (nonneg_of_mul_nonneg_right hv hs) (nonneg_of_mul_nonneg_right hk (sq_pos_of_pos hs)) ζ hζ

attribute [-instance] SimpleGraph.fintypeEdgeSetSup
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- This is the actual graph logarithm, for every physical arm pair. -/
theorem graph_lower (C : SimpleGraph V) (u : V) (p q : ℕ)
    (hd : 46 ≤ C.degree u) (y : ℝ) (hy : (1/2 : ℝ) ≤ y) :
    TailIntegral.phi y ≤ MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y := by
  have hy0 : 0 < y := by linarith
  have h := log_lower (C.degree u) y (PathEnclosure.arm y p) (PathEnclosure.arm y q)
    (by exact_mod_cast hd) hy
    ⟨PathEnclosure.arm_nonneg y p,PathEnclosure.arm_le_one y hy0 p⟩
    ⟨PathEnclosure.arm_nonneg y q,PathEnclosure.arm_le_one y hy0 q⟩
    _ (schur_in_disk C u y hy0).1
  change TailIntegral.phi y ≤ Real.log ‖(shifted (z y) (source C u p q)).det /
    (shifted (z y) (fused C u p q)).det‖
  rw [concrete_graph_quotient C u y hy0 p q]
  exact h

/-- The original middle/tail comparisons are discharged. Low-strip and escape
remain explicit original graph obligations. -/
theorem strict_fusion_of_lowstrip_escape {m : ℕ} (C : SimpleGraph (Fin m))
    (u : Fin m) (p q : ℕ) (hT : (source C u p q).IsTree) (hd : 46 ≤ C.degree u)
    (hlow : (-(8/3 : ℝ)*Real.log 2-2*Real.log 3)/(C.degree u : ℝ)-Real.log 2/2 ≤
      ∫ y : ℝ in (0 : ℝ)..(1/2), MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y)
    (hescape : ∀ y ∈ Icc ((653/2000 : ℝ)*(C.degree u : ℝ)) (10*(C.degree u : ℝ)),
      TailIntegral.escapeDensity (C.degree u) y ≤
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y) :
    laplacianEnergy (fused C u p q) < laplacianEnergy (source C u p q) := by
  apply TailIntegral.strict_fusion_of_four_regions C u p q hT hd hlow
  · intro y hy
    exact graph_lower C u p q hd y hy.1
  · exact hescape
  · intro y hy
    apply graph_lower C u p q hd y
    have hd' : (46 : ℝ) ≤ C.degree u := by exact_mod_cast hd
    change 10*(C.degree u : ℝ) < y at hy
    linarith

#print axioms x_rescale
#print axioms t_rescale
#print axioms c_rescale
#print axioms v_rescale
#print axioms k_rescale
#print axioms log_lower
#print axioms graph_lower
#print axioms strict_fusion_of_lowstrip_escape
attribute [instance] SimpleGraph.fintypeEdgeSetSup
end
end Gebendorfer.RadenkovicGutman.HighDegreeTail

/-! Exact physical-parity boxes required by the original low-strip producer.
The index is one less than physical length. These enclosures alone do not
prove the remaining low-strip polynomial signs or its integral. -/
namespace Gebendorfer.RadenkovicGutman.LowStripParity
open PathEnclosure Set
noncomputable section

theorem step_lower (y a : ℝ) (hy : 0 < y) (ha : 0 ≤ a) (hb : a ≤ y) :
    y/(1+y) ≤ y^2/(y^2+a) := by
  apply (div_le_div_iff₀ (by positivity : 0 < 1+y) (by positivity : 0 < y^2+a)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hb hy.le]

theorem step_upper (y b : ℝ) (hy : 0 < y) (hb : 0 ≤ b) (hl : y/(1+y) ≤ b) :
    y^2/(y^2+b) ≤ y := by
  have hh : y-y^2 ≤ y/(1+y) := by
    apply (le_div_iff₀ (by positivity : 0 < 1+y)).mpr
    nlinarith only [pow_nonneg hy.le 3]
  have he : y ≤ y^2+b := by linarith only [hh,hl]
  apply (div_le_iff₀ (by positivity : 0 < y^2+b)).mpr
  nlinarith only [mul_le_mul_of_nonneg_left he hy.le]

theorem parity_bounds (y : ℝ) (hy : 0 < y) (n : ℕ) :
    arm y (2*n) ≤ y ∧ y/(1+y) ≤ arm y (2*n+1) := by
  induction n with
  | zero =>
    constructor
    · change (0 : ℝ) ≤ y
      exact hy.le
    · change y/(1+y) ≤ y^2/(y^2+0)
      exact step_lower y 0 hy (by norm_num) hy.le
  | succ n ih =>
    have he : arm y (2*(n+1)) ≤ y := by
      rw [show 2*(n+1)=(2*n+1)+1 by omega,arm]
      exact step_upper y _ hy (arm_nonneg y _) ih.2
    refine ⟨he,?_⟩
    change y/(1+y) ≤ y^2/(y^2+arm y (2*(n+1)))
    exact step_lower y _ hy (arm_nonneg y _) he

/-- Every odd physical arm has the original low-strip form alpha=y*A. -/
theorem odd_physical_parameter (y : ℝ) (hy : 0 < y) (n : ℕ) :
    ∃ a ∈ Icc (0 : ℝ) 1, arm y (2*n)=y*a := by
  refine ⟨arm y (2*n)/y,⟨div_nonneg (arm_nonneg y _) hy.le,
    (div_le_one hy).mpr (parity_bounds y hy n).1⟩,?_⟩
  field_simp [hy.ne']

/-- Every even physical arm has the original form alpha=(y+A)/(1+y). -/
theorem even_physical_parameter (y : ℝ) (hy : 0 < y) (n : ℕ) :
    ∃ a ∈ Icc (0 : ℝ) 1, arm y (2*n+1)=(y+a)/(1+y) := by
  let a := (1+y)*arm y (2*n+1)-y
  have hlow := (div_le_iff₀ (by positivity : 0 < 1+y)).mp (parity_bounds y hy n).2
  have hhigh := mul_le_mul_of_nonneg_left (arm_le_one y hy (2*n+1)) (by positivity : 0 ≤ 1+y)
  refine ⟨a,⟨?_,?_⟩,?_⟩
  · dsimp [a]
    nlinarith only [hlow]
  · dsimp [a]
    nlinarith only [hhigh]
  · apply (eq_div_iff (by positivity : 1+y ≠ 0)).mpr
    dsimp [a]
    ring

theorem actual_parameter (y : ℝ) (hy : 0 < y) (p : ℕ) :
    (p%2=0 ∧ ∃ a ∈ Icc (0 : ℝ) 1, arm y p=y*a) ∨
    (p%2=1 ∧ ∃ a ∈ Icc (0 : ℝ) 1, arm y p=(y+a)/(1+y)) := by
  by_cases h : p%2=0
  · left
    refine ⟨h,?_⟩
    have he : 2*(p/2)=p := by omega
    simpa only [he] using odd_physical_parameter y hy (p/2)
  · right
    refine ⟨by omega,?_⟩
    have he : 2*(p/2)+1=p := by omega
    simpa only [he] using even_physical_parameter y hy (p/2)

#print axioms step_lower
#print axioms step_upper
#print axioms parity_bounds
#print axioms odd_physical_parameter
#print axioms even_physical_parameter
#print axioms actual_parameter
end
end Gebendorfer.RadenkovicGutman.LowStripParity
