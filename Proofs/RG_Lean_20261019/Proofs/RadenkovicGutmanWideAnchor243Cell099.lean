/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor243Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor243Cell099
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (269581/1048576)
  b := (323497/1048576)
  s := [(7605434397949/17592186044416),(-717142091931/17592186044416),(17352883281/8796093022208)]
  L := [(44540389154057368173/73786976294838206464),(91613808425/1099511627776),(-13867581227/6597069766656),(-57569739/137438953472),(27656375/412316860416)]
  c := (663703518421/1099511627776)
  R := (-12619646102291/50000000000000)
  total := (-70689445571/6250000000000)
  k := 1
  n := 32
  sFloor := (1730749518145/8796093022208)
  nFloor := (173625377269/268435456)
  eFloor := (455998679307/1073741824)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=269581,width:=53916,den:=1048576,localDen:=221360928884514619392,lowerC:=133621167462109151232,s:=[95698511751165247488,-9023735834263683072,436699606542188544],L:=[133621167462172104519,18444295830346137600,-465318811285848064,-92722554841595904,14847903268864000],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor243Source.source.poly i) 269581 53916 1048576
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor243Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 25) (CoreQuotient.fused G u 0 25) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 25 WideAnchor243Source.data
    WideAnchor243Source.path_checked WideAnchor243Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor243Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 25 0) (CoreQuotient.fused G u 25 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 25 0 WideAnchor243Source.data
    WideAnchor243Source.path_swapped WideAnchor243Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor243Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor243Cell099
