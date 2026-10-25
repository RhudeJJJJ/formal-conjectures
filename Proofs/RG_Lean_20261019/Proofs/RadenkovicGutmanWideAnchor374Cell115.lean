/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor374Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor374Cell115
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1246027/262144)
  b := (23363/4096)
  s := [(2215317396617/562949953421312),(-1151391868877/562949953421312),(281221483505/562949953421312)]
  L := [(2519517187638527468883/2361183241434822606848),(-138593092051/6597069766656),(14711359739/3298534883328),(-292730855/412316860416),(14447905/206158430208)]
  c := (577171497387/549755813888)
  R := (2433261998129/100000000000000)
  total := (208889544879/7812500000000)
  k := 0
  n := 32
  sFloor := (1345147011245/1125899906842624)
  nFloor := 20800035440781600835502080
  eFloor := 19340083939320832832045056
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1246027,width:=249205,den:=262144,localDen:=7083549724304467820544,lowerC:=7436798116381543366656,s:=[27875143853700808704,-14487862563594829824,3538585179452866560],L:=[7558551562915582406649,-148813199452640641024,31592404479348047872,-5029077795020472320,496426235765719040],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor374Source.source.poly i) 1246027 249205 262144
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor374Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 12) (CoreQuotient.fused G u 2 12) (((21/11) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (21/11) 2 12 WideAnchor374Source.data
    WideAnchor374Source.path_checked WideAnchor374Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor374Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 12 2) (CoreQuotient.fused G u 12 2) (((21/11) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (21/11) 12 2 WideAnchor374Source.data
    WideAnchor374Source.path_swapped WideAnchor374Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor374Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor374Cell115
