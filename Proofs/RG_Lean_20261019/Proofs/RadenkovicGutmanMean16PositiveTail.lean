/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanMean16PolynomialBase
import Proofs.RadenkovicGutmanInversePolynomialNorm
import Proofs.RadenkovicGutmanRationalPolynomialOrder
import Proofs.RadenkovicGutmanQuantitativePositiveTail

namespace Gebendorfer.RadenkovicGutman.Mean16PositiveTail
open CoreQuotient GeneralGraphQuotient Polynomial PolynomialPathMap RationalComplexPolynomial
open Mean16PolynomialBase Set MeasureTheory
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def scale : ℚ[X] := C 2*X^3
def denominator : ℚ[X] := (scale+1)*ofList us+(scale^2+scale)*ofList vs
def comparison : ℚ[X] := X^2*(scale*ofList js-denominator)-C (1991937/1000000)*denominator
def comparisonCoefficients : List ℚ := [(22945302198593045288314477189070482886867/81920),(14868107516731526653992296629392350273880784503/655360000),(2669110230291396409810067162428944735624337132819/838860800000),(1768804021733889594289279234865273726077089594271/8388608000000),(37662575452077646214206882947487266878273038039967/4294967296000000),(268887439923648857995198374412459976994929251/1048576000000),(375761272867958115134879932553158792301723413/67108864000000),(203173108492895615156532534954805369998326687/2147483648000000),(663143313794728731065312082218186764353/524288000000),(227552801431997268042858943030575035981/16777216000000),(481398902841499572358204900376337/4096000000),(432499478238272074079588419059121/524288000000),(1197796914656936479603057123/256000000),(43593544469471732963387467/2048000000),(306474316406057622261/4000000),(27316283045328302353/128000000),(6934856162811/15625),(649018646029/1000000),(9304608/15625),(8063/31250)]
def nCoefficients : List ℚ := [(1153470234163920625/4),(4613332133841452785/256),(32290032413042786033/65536),(15395779055843/2),(76973662605539/1024),469786000,(29360627/16),4096,4]
def eCoefficients : List ℚ := [(1153329464461895537/4),(4612909856950462321/256),(32287921157442512753/65536),(15395107936483/2),(76971649308899/1024),469779856,(29360499/16),4096,4]

theorem comparison_checked : RationalPolynomialOrder.rayAccepts comparison 128 comparisonCoefficients = true := by
  rw [RationalPolynomialOrder.rayAccepts,decide_eq_true_eq]
  constructor
  · apply Polynomial.funext
    intro t
    norm_num [comparison,denominator,scale,us,vs,js,ns,sep,comparisonCoefficients,ofList,RationalPolynomialCell.affine]
    ring
  · decide +kernel
theorem n_checked : RationalPolynomialOrder.rayAccepts (ofList ns) 128 nCoefficients = true := by
  rw [RationalPolynomialOrder.rayAccepts,decide_eq_true_eq]
  constructor
  · apply Polynomial.funext
    intro t
    norm_num [comparison,denominator,scale,us,vs,js,ns,sep,nCoefficients,ofList,RationalPolynomialCell.affine]
    ring
  · decide +kernel
theorem e_checked : RationalPolynomialOrder.rayAccepts (ofList sep) 128 eCoefficients = true := by
  rw [RationalPolynomialOrder.rayAccepts,decide_eq_true_eq]
  constructor
  · apply Polynomial.funext
    intro t
    norm_num [comparison,denominator,scale,us,vs,js,ns,sep,eCoefficients,ofList,RationalPolynomialCell.affine]
    ring
  · decide +kernel
theorem n_constant_positive : 0 < nCoefficients.headD 0 := by decide +kernel
theorem e_constant_positive : 0 < eCoefficients.headD 0 := by decide +kernel

theorem actual_squared_norm {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u = 1) (y : ℝ) (hy : 128 ≤ y) :
    1+(1991937/1000000 : ℝ)/y^2 ≤
      ‖(shifted (point (15/8) y) (source G u 0 0)).det /
        (shifted (point (15/8) y) (fused G u 0 0)).det‖^2 := by
  have hy0 : 0 < y := by linarith
  have hM : 0 < 2*y^3 := by positivity
  have hN := RationalPolynomialOrder.ray_positive (ofList ns) 128 nCoefficients n_checked
    n_constant_positive y (by simpa using hy)
  have hE := RationalPolynomialOrder.ray_positive (ofList sep) 128 eCoefficients e_checked
    e_constant_positive y (by simpa using hy)
  have hP := RationalPolynomialOrder.ray_nonneg comparison 128 comparisonCoefficients
    comparison_checked y (by simpa using hy)
  simp only [comparison,denominator,scale,map_sub,map_mul,map_add,map_pow,map_one,
    real_C,real_X,Rat.cast_div,Rat.cast_ofNat] at hP
  have hb := InversePolynomialNorm.reserve_bound _ _ _ (1991937/1000000) y hy0 hP
  have hi := InversePolynomialNorm.inverse_parameter _ _ _ (2*y^3) (1+(1991937/1000000)/y^2) hM hb
  simpa only [Rat.cast_div,Rat.cast_ofNat] using
    (GeneralPathPolynomialPayments.actual_norm_lower (15/8) y hy0 0 0 as bs cs es us vs js ns sep
    path_checked norms_checked (1/(2*y^3)) (1+(1991937/1000000)/y^2) (by positivity) hN hE hi G u hd)

theorem actual_logarithm {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u = 1) (y : ℝ) (hy : 128 ≤ y) :
    QuantitativePositiveTail.coefficient (1991937/1000000) 128/y^2 ≤
      MixedGraphIntegral.logarithm (source G u 0 0) (fused G u 0 0) (15/8) y := by
  exact QuantitativePositiveTail.pointwise (1991937/1000000) 128 y _
    (by norm_num) (by norm_num) hy (actual_squared_norm G u hd y hy)

theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u = 1) :
    (127483968/16385991937 : ℝ) ≤ ∫ y : ℝ in Ioi 128,
      MixedGraphIntegral.logarithm (source G u 0 0) (fused G u 0 0) (15/8) y := by
  have hf := (ActualFusionIntegral.logarithm_integrable G u 0 0 (15/8)).mono_set
    (show Ioi (128 : ℝ) ⊆ Ioi 0 from fun y hy => lt_trans (by norm_num : (0 : ℝ) < 128) hy)
  have h := QuantitativePositiveTail.integral_lower _ (1991937/1000000) 128
    (by norm_num) (by norm_num) hf (fun y hy => actual_logarithm G u hd y hy.le)
  norm_num [QuantitativePositiveTail.coefficient] at h
  exact h

#print axioms comparison_checked
#print axioms n_checked
#print axioms e_checked
#print axioms n_constant_positive
#print axioms e_constant_positive
#print axioms actual_squared_norm
#print axioms actual_logarithm
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.Mean16PositiveTail
