/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor035Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor035Cell031
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (583371/549755813888)
  b := (700045/549755813888)
  s := [(4398046510607/4398046511104),(-197/4398046511104),(-11/2199023255552)]
  L := [(5740936793797/151115727451828646838272),(2296370781093/151115727451828646838272),(344455026799/226673591177742970257408),(-7/9444732965739290427392),(5/14167099448608935641088)]
  c := (1435234198449/37778931862957161709568)
  R := (-239936893856781/20000000000000)
  total := (-2526182897/1000000000000000)
  k := 35
  n := 32
  sFloor := (1099511627597/2199023255552)
  nFloor := (774086077775/18889465931478580854784)
  eFloor := (575136432667/9444732965739290427392)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=583371,width:=116674,den:=549755813888,localDen:=453347182355485940514816,lowerC:=17222810381388,s:=[453347182304255570608128,-20306605375488,-2267742732288],L:=[17222810381391,6889112343279,688910053598,-336,160],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor035Source.source.poly i) 583371 116674 549755813888
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor035Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 10 14) (CoreQuotient.fused G u 10 14) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 10 14 WideAnchor035Source.data
    WideAnchor035Source.path_checked WideAnchor035Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor035Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 14 10) (CoreQuotient.fused G u 14 10) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 14 10 WideAnchor035Source.data
    WideAnchor035Source.path_swapped WideAnchor035Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor035Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor035Cell031
