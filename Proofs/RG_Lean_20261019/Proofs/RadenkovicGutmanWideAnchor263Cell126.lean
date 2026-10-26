/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor263Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor263Cell126
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (144657/4096)
  b := (1388707/32768)
  s := [(1631815336743/144115188075855872),(-7474961613885/1152921504606846976),(990413673917/576460752303423488)]
  L := [(591226948887518568375/590295810358705651712),(-1374215803/2199023255552),(202621275/1099511627776),(-6182537/137438953472),(479521/68719476736)]
  c := (1100719733853/1099511627776)
  R := (3431758983/6250000000000)
  total := (4646436393603/1000000000000000)
  k := 0
  n := 32
  sFloor := (1890097106973/576460752303423488)
  nFloor := 28653023062255059994878234779247834157272599419177606049565966253147264543863956295534157388650256465187886367231941143126015567986688
  eFloor := 28607248661384087416352888663340336113925195447964167493484639840659892214688174627545657842540358358202856381369739135066941964681216
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1157256,width:=231451,den:=32768,localDen:=590295810358705651712,lowerC:=590944407370057383936,s:=[6683915619299328,-3827180346309120,1014183602091008],L:=[591226948887518568375,-368888245720711168,108781468699852800,-26553794221309952,4119054025490432],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor263Source.source.poly i) 1157256 231451 32768
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor263Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 39) (CoreQuotient.fused G u 0 39) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 39 WideAnchor263Source.data
    WideAnchor263Source.path_checked WideAnchor263Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor263Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 39 0) (CoreQuotient.fused G u 39 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 39 0 WideAnchor263Source.data
    WideAnchor263Source.path_swapped WideAnchor263Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor263Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor263Cell126
