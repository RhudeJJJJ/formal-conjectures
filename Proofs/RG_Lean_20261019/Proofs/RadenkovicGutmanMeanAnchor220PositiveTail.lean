/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanMeanAnchor220PolynomialBase
import Proofs.RadenkovicGutmanInversePolynomialNorm
import Proofs.RadenkovicGutmanRationalPolynomialOrder
import Proofs.RadenkovicGutmanQuantitativePositiveTail

namespace Gebendorfer.RadenkovicGutman.MeanAnchor220PositiveTail
open CoreQuotient GeneralGraphQuotient Polynomial PolynomialPathMap RationalComplexPolynomial
open MeanAnchor220PolynomialBase Set MeasureTheory
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def scale : ℚ[X] := C 2*X^3
def denominator : ℚ[X] := (scale+1)*ofList us+(scale^2+scale)*ofList vs
def comparison : ℚ[X] := X^2*(scale*ofList js-denominator)-C ((398397/200000))*denominator
def comparisonCoefficients : List ℚ := [(140714715762215535180346772033997332268842167861964/2912260640310125),(5217665998557057155937688675328118075140059096059220863/232980851224810000),(937658060478097516694077338396797558848930026587575886203/298215489567756800000),(37363167162326857591616743653964149060113140175067119/179216039403700000),(10346713799674783293782613443101813747452415668913935139/1192861958271027200000),(18917624932569143122740109362219305035713659911475963/74553872391939200000),(165288022232994146077359235155384349443669405969341/29821548956775680000),(55875715377004043516530046611250529879177846991459/596430979135513600000),(212577965643247596221862142018048121057031/169671989968000),(5928684868869294372694803386187070229494177/441147173916800000),(4751329784608099549066757485280988999/40786536050000),(1067518660838891383890510477775559213/1305169153600000),(4479872371500569222237267939279/965361800000),(10193508471237504872007361823/482680900000),(10858948924100171406111/142805000),(605109940777542799373/2856100000),(93111316774767/211250),(272402737069/422500),(1849248/3125),(1603/6250)]
def nCoefficients : List ℚ := [(1391906226955996011148288/4826809),(86983618112986866298576/4826809),(38051387894875286096621/77228944),(219860048877055360/28561),(8587689585097691/114244),(79393901824/169),(310121711/169),4096,4]
def eCoefficients : List ℚ := [(1391736354457187672069120/4826809),(86975656031124254661712/4826809),(38048899917164120803781/77228944),(219850464896292224/28561),(8587464968352299/114244),(79392863488/169),(310120359/169),4096,4]

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
    1+((398397/200000) : ℝ)/y^2 ≤
      ‖(shifted (point (51/26) y) (source G u 0 0)).det /
        (shifted (point (51/26) y) (fused G u 0 0)).det‖^2 := by
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
  have hb := InversePolynomialNorm.reserve_bound _ _ _ ((398397/200000)) y hy0 hP
  have hi := InversePolynomialNorm.inverse_parameter _ _ _ (2*y^3) (1+((398397/200000))/y^2) hM hb
  simpa only [Rat.cast_div,Rat.cast_ofNat] using
    (GeneralPathPolynomialPayments.actual_norm_lower (51/26) y hy0 0 0 as bs cs es us vs js ns sep
    path_checked norms_checked (1/(2*y^3)) (1+((398397/200000))/y^2) (by positivity) hN hE hi G u hd)

theorem actual_logarithm {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u = 1) (y : ℝ) (hy : 128 ≤ y) :
    QuantitativePositiveTail.coefficient ((398397/200000)) 128/y^2 ≤
      MixedGraphIntegral.logarithm (source G u 0 0) (fused G u 0 0) (51/26) y := by
  exact QuantitativePositiveTail.pointwise ((398397/200000)) 128 y _
    (by norm_num) (by norm_num) hy (actual_squared_norm G u hd y hy)

theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u = 1) :
    ((25497408/3277198397) : ℝ) ≤ ∫ y : ℝ in Ioi 128,
      MixedGraphIntegral.logarithm (source G u 0 0) (fused G u 0 0) (51/26) y := by
  have hf := (ActualFusionIntegral.logarithm_integrable G u 0 0 (51/26)).mono_set
    (show Ioi (128 : ℝ) ⊆ Ioi 0 from fun y hy => lt_trans (by norm_num : (0 : ℝ) < 128) hy)
  have h := QuantitativePositiveTail.integral_lower _ ((398397/200000)) 128
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
end Gebendorfer.RadenkovicGutman.MeanAnchor220PositiveTail
