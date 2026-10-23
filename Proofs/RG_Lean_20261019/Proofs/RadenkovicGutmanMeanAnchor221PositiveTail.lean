/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanMeanAnchor221PolynomialBase
import Proofs.RadenkovicGutmanInversePolynomialNorm
import Proofs.RadenkovicGutmanRationalPolynomialOrder
import Proofs.RadenkovicGutmanQuantitativePositiveTail

namespace Gebendorfer.RadenkovicGutman.MeanAnchor221PositiveTail
open CoreQuotient GeneralGraphQuotient Polynomial PolynomialPathMap RationalComplexPolynomial
open MeanAnchor221PolynomialBase Set MeasureTheory
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def scale : ℚ[X] := C 2*X^3
def denominator : ℚ[X] := (scale+1)*ofList us+(scale^2+scale)*ofList vs
def comparison : ℚ[X] := X^2*(scale*ofList js-denominator)-C ((1991959/1000000))*denominator
def comparisonCoefficients : List ℚ := [(6852913739408730137983228751427819910420207417488048128/68483201350063503125),(7719229372489095635621517332465272601905826695984656289792/342416006750317515625),(1083397356782183674163107891701435559914720303471652950544/342416006750317515625),(14363971713956261343892471290043972836930470239559789568/68483201350063503125),(597497678174262090964595547852056380044612355088786518/68483201350063503125),(17475968636705340181272476567605664537038118727176112/68483201350063503125),(30532972743451762689452880782125586534086964888048673/5478656108005080250000),(32249651673452351721700415902837604404952271268096/342416006750317515625),(1304245491150417310810211409992168919594698837/1035662780341225000),(1520419476516840456725294344438439815085311/112572041341437500),(2291629196218743133417175956242570025137/19577746320250000),(2010897774155782261216139355807151051/2447218290031250),(21563857236038513413445993112911/4626121531250),(39246384605813132536260322873/1850448612500),(333856503130975824666006/4372515625),(1860078265436872562589/8745031250),(7313834316603257/16531250),(5348335301791/8265625),(9277856/15625),(8041/31250)]
def nCoefficients : List ℚ := [(42688883131887871918342144/148035889),(2667735727539625245749248/148035889),(72938411948379103545136/148035889),(2154187540221368320/279841),(21035548180560844/279841),(248516878336/529),(970735840/529),4096,4]
def eCoefficients : List ℚ := [(42683673317319423441502208/148035889),(2667491537244652813766656/148035889),(72933642915461519777104/148035889),(2154093636603318272/279841),(21034997981861320/279841),(248513628160/529),(970731608/529),4096,4]

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
    1+((1991959/1000000) : ℝ)/y^2 ≤
      ‖(shifted (point (44/23) y) (source G u 0 0)).det /
        (shifted (point (44/23) y) (fused G u 0 0)).det‖^2 := by
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
  have hb := InversePolynomialNorm.reserve_bound _ _ _ ((1991959/1000000)) y hy0 hP
  have hi := InversePolynomialNorm.inverse_parameter _ _ _ (2*y^3) (1+((1991959/1000000))/y^2) hM hb
  simpa only [Rat.cast_div,Rat.cast_ofNat] using
    (GeneralPathPolynomialPayments.actual_norm_lower (44/23) y hy0 0 0 as bs cs es us vs js ns sep
    path_checked norms_checked (1/(2*y^3)) (1+((1991959/1000000))/y^2) (by positivity) hN hE hi G u hd)

theorem actual_logarithm {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u = 1) (y : ℝ) (hy : 128 ≤ y) :
    QuantitativePositiveTail.coefficient ((1991959/1000000)) 128/y^2 ≤
      MixedGraphIntegral.logarithm (source G u 0 0) (fused G u 0 0) (44/23) y := by
  exact QuantitativePositiveTail.pointwise ((1991959/1000000)) 128 y _
    (by norm_num) (by norm_num) hy (actual_squared_norm G u hd y hy)

theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u = 1) :
    ((127485376/16385991959) : ℝ) ≤ ∫ y : ℝ in Ioi 128,
      MixedGraphIntegral.logarithm (source G u 0 0) (fused G u 0 0) (44/23) y := by
  have hf := (ActualFusionIntegral.logarithm_integrable G u 0 0 (44/23)).mono_set
    (show Ioi (128 : ℝ) ⊆ Ioi 0 from fun y hy => lt_trans (by norm_num : (0 : ℝ) < 128) hy)
  have h := QuantitativePositiveTail.integral_lower _ ((1991959/1000000)) 128
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
end Gebendorfer.RadenkovicGutman.MeanAnchor221PositiveTail
