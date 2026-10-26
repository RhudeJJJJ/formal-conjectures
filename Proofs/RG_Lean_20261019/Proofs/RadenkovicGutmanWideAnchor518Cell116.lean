/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor518Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor518Cell116
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (23363/4096)
  b := (897139/131072)
  s := [(5372322885521/2251799813685248),(-5735340055583/4503599627370496),(716383958203/2251799813685248)]
  L := [(77453393460966648269/73786976294838206464),(-54748980443/3298534883328),(12835428727/3298534883328),(-74285885/103079215104),(17832797/206158430208)]
  c := (71217315159/68719476736)
  R := (357033160757/20000000000000)
  total := (23749884251807/1000000000000000)
  k := 0
  n := 32
  sFloor := (805259203983/1125899906842624)
  nFloor := 5655734617014009856
  eFloor := 5362360361905291264
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=747616,width:=149523,den:=131072,localDen:=221360928884514619392,lowerC:=229407029637622530048,s:=[528120828938256384,-281903434412015616,70423408627187712],L:=[232360180382899944807,-3674141882687946752,861371040821936128,-159527723314708480,19147819977801728],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor518Source.source.poly i) 747616 149523 131072
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor518Source.source witness geometry=true := by
  unfold IntegerPolynomialPaymentCell.checks
  rw [decide_eq_true_eq]
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by intro i; rfl,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩
theorem budget : SemanticPolynomialPaymentCell.Budget witness := by
  unfold SemanticPolynomialPaymentCell.Budget
  decide +kernel
theorem logarithm_checked : RationalLog.accepts witness.c witness.R witness.k witness.n=true := by decide +kernel
noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 4) (CoreQuotient.fused G u 4 4) (((32/17) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (32/17) 4 4 WideAnchor518Source.data
    WideAnchor518Source.path_checked WideAnchor518Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor518Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 4) (CoreQuotient.fused G u 4 4) (((32/17) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (32/17) 4 4 WideAnchor518Source.data
    WideAnchor518Source.path_swapped WideAnchor518Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor518Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor518Cell116
