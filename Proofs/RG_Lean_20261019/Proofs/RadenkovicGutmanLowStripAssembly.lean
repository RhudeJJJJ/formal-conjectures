/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanLowStripIntegral
import Proofs.RadenkovicGutmanTailIntegral

/-! Exact integration and gap-free assembly of the original two low strips.
Only their original pointwise graph comparisons remain as premises. -/
namespace Gebendorfer.RadenkovicGutman.LowStripPrimitive
open Real Set Filter MeasureTheory
open scoped Topology
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false

theorem arsinh_div_integrable (A B : ℝ) (hA : 0 ≤ A) :
    IntegrableOn (fun s : ℝ => arsinh (A/s)) (Ioc 0 B) := by
  have hk : IntegrableOn (ScalarIntegral.kernel A) (Ioc 0 B) :=
    (ScalarIntegral.kernel_integrable A hA).mono_set Ioc_subset_Ioi_self
  have hc : IntegrableOn (fun _ : ℝ => log 2) (Ioc 0 B) :=
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => log 2) volume 0 B).1
  have hcont : ContinuousOn (fun s : ℝ => arsinh (A/s)) (Ioc 0 B) := by
    intro s hs
    exact ((continuousAt_const.div continuousAt_id hs.1.ne').arsinh).continuousWithinAt
  apply (hk.add hc).mono' (hcont.aestronglyMeasurable measurableSet_Ioc)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  have hspos : 0 < s := hs.1
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.arsinh_nonneg_iff.mpr (div_nonneg hA hspos.le))]
  have h := arsinh_upper (A/s) (div_nonneg hA hspos.le)
  dsimp [ScalarIntegral.kernel]
  linarith

theorem scaled_arsinh_integrable (d B : ℝ) (hd : 0 < d) (hB : 0 ≤ B) :
    IntervalIntegrable (fun y : ℝ => arsinh (2/(d*y))) volume 0 B := by
  have he : (fun y : ℝ => arsinh (2/(d*y))) = fun y => arsinh ((2/d)/y) := by
    funext y
    congr 1
    ring
  rw [he]
  refine ⟨arsinh_div_integrable (2/d) B (by positivity), ?_⟩
  simp [show Ioc B (0 : ℝ) = ∅ from Ioc_eq_empty_of_le hB]

theorem scaled_primitive_derivative (d y : ℝ) (hd : 0 < d) (hy : 0 < y) :
    HasDerivAt (fun t : ℝ => primitive (d*t)/d) (arsinh (2/(d*y))) y := by
  have h := ((primitive_derivative (d*y) (mul_pos hd hy)).comp y
    ((hasDerivAt_id y).const_mul d)).div_const d
  convert! h using 1
  dsimp only [id]
  field_simp [hd.ne']

theorem scaled_arsinh_integral (d B : ℝ) (hd : 0 < d) (hB : 0 < B) :
    (∫ y : ℝ in 0..B, arsinh (2/(d*y))) = primitive (d*B)/d := by
  have hcont : Continuous (fun y : ℝ => primitive (d*y)/d) :=
    (primitive_continuous.comp (by fun_prop)).div_const d
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hB.le
    hcont.continuousOn (fun y hy => scaled_primitive_derivative d y hd hy.1)
    (scaled_arsinh_integrable d B hd hB.le)
  simpa only [mul_zero,primitive_zero,zero_div,sub_zero] using h

theorem original_lowstrip_lower (f : ℝ → ℝ) (d : ℝ) (hd : 46 ≤ d)
    (hf : IntegrableOn f (Ioi 0))
    (htangent : ∀ y ∈ Ioc (0 : ℝ) (8/(3*d)), -arsinh (2/(d*y))-log 2 ≤ f y)
    (hconstant : ∀ y ∈ Icc (8/(3*d) : ℝ) (1/2), -log 2 ≤ f y) :
    (-(8/3 : ℝ)*log 2-2*log 3)/d-log 2/2 ≤ ∫ y : ℝ in (0 : ℝ)..(1/2), f y := by
  have hd0 : 0 < d := by linarith only [hd]
  let cut : ℝ := 8/(3*d)
  have hcut : 0 < cut := by dsimp [cut]; positivity
  have hcutHalf : cut ≤ (1/2 : ℝ) := by
    dsimp [cut]
    apply (div_le_iff₀ (by positivity : 0 < 3*d)).mpr
    linarith only [hd]
  have he : d*cut=8/3 := by dsimp [cut]; field_simp [hd0.ne']
  have hi := scaled_arsinh_integrable d cut hd0 hcut.le
  have hm : IntervalIntegrable (fun y : ℝ => -arsinh (2/(d*y))-log 2) volume 0 cut :=
    hi.neg.sub intervalIntegrable_const
  have hf1 := TailIntegral.interval_integrable_of_Ioi hf (by norm_num : (0 : ℝ) ≤ 0) hcut.le
  have hf2 := TailIntegral.interval_integrable_of_Ioi hf hcut.le hcutHalf
  have ht : (∫ y : ℝ in (0 : ℝ)..cut, -arsinh (2/(d*y))-log 2) ≤
      ∫ y : ℝ in (0 : ℝ)..cut, f y := by
    simp only [intervalIntegral.integral_of_le hcut.le]
    apply integral_mono_ae hm.1 hf1.1
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    exact htangent y hy
  rw [intervalIntegral.integral_sub hi.neg intervalIntegrable_const,
    intervalIntegral.integral_neg,scaled_arsinh_integral d cut hd0 hcut,
    he,primitive_eight_thirds,intervalIntegral.integral_const] at ht
  simp only [sub_zero,smul_eq_mul] at ht
  have hc : (∫ _y : ℝ in cut..(1/2), -log 2) ≤ ∫ y : ℝ in cut..(1/2), f y := by
    exact intervalIntegral.integral_mono_on hcutHalf intervalIntegrable_const hf2 hconstant
  rw [intervalIntegral.integral_const] at hc
  simp only [smul_eq_mul] at hc
  have hadd := intervalIntegral.integral_add_adjacent_intervals hf1 hf2
  calc
    (-(8/3 : ℝ)*log 2-2*log 3)/d-log 2/2 =
      ( -((8/3)*log 2+2*log 3)/d-cut*log 2)+((1/2-cut)*(-log 2)) := by ring
    _ ≤ (∫ y : ℝ in (0 : ℝ)..cut, f y)+(∫ y : ℝ in cut..(1/2), f y) := add_le_add ht hc
    _ = ∫ y : ℝ in (0 : ℝ)..(1/2), f y := hadd

attribute [-instance] SimpleGraph.fintypeEdgeSetSup
open CoreQuotient
open scoped Classical

theorem original_graph_lowstrip_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : 46 ≤ C.degree u)
    (htangent : ∀ y ∈ Ioc (0 : ℝ) (8/(3*(C.degree u : ℝ))),
      -arsinh (2/((C.degree u : ℝ)*y))-log 2 ≤
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y)
    (hconstant : ∀ y ∈ Icc (8/(3*(C.degree u : ℝ)) : ℝ) (1/2), -log 2 ≤
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y) :
    (-(8/3 : ℝ)*log 2-2*log 3)/(C.degree u : ℝ)-log 2/2 ≤
      ∫ y : ℝ in (0 : ℝ)..(1/2),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y := by
  exact original_lowstrip_lower _ (C.degree u) (by exact_mod_cast hd)
    (ActualFusionIntegral.logarithm_integrable C u p q 2) htangent hconstant

#print axioms scaled_arsinh_integral
#print axioms original_lowstrip_lower
#print axioms original_graph_lowstrip_lower
attribute [instance] SimpleGraph.fintypeEdgeSetSup
end
end Gebendorfer.RadenkovicGutman.LowStripPrimitive
