/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor532Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor532Cell112
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (721081/262144)
  b := (865297/262144)
  s := [(4426629490931/281474976710656),(-3996572521283/562949953421312),(432513114537/281474976710656)]
  L := [(168380019220666085921/147573952589676412928),(-128483451585/4398046511104),(13898595811/6597069766656),(147661773/274877906944),(-67318291/412316860416)]
  c := (1225135605503/1099511627776)
  R := (540927148853/10000000000000)
  total := (32925730214959/1000000000000000)
  k := 0
  n := 32
  sFloor := (1430428172413/281474976710656)
  nFloor := 6611077871349792768
  eFloor := 5614748894312267776
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=721081,width:=144216,den:=262144,localDen:=442721857769029238784,lowerC:=493304752387550871552,s:=[6962486167623696384,-3143032521057632256,680284307383123968],L:=[505140057661998257763,-12933567718002524160,932718976071368704,237825932214140928,-72282464566902784],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor532Source.source.poly i) 721081 144216 262144
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor532Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 5 10) (CoreQuotient.fused G u 5 10) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 5 10 WideAnchor532Source.data
    WideAnchor532Source.path_checked WideAnchor532Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor532Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 10 5) (CoreQuotient.fused G u 10 5) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 10 5 WideAnchor532Source.data
    WideAnchor532Source.path_swapped WideAnchor532Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor532Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor532Cell112
