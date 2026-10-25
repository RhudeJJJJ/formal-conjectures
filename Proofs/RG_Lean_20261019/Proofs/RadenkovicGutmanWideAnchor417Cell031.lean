/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor417Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor417Cell031
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (583371/549755813888)
  b := (700045/549755813888)
  s := [(4398046511011/4398046511104),(-39/4398046511104),(-1/2199023255552)]
  L := [(4048218430661/302231454903657293676544),(1619284596503/302231454903657293676544),(242892273107/453347182355485940514816),(-1/18889465931478580854784),(1/28334198897217871282176)]
  c := (1012054607665/75557863725914323419136)
  R := (-1251809103853727/100000000000000)
  total := (-2636806367/1000000000000000)
  k := 37
  n := 32
  sFloor := (2199023255485/4398046511104)
  nFloor := (1006723021519/37778931862957161709568)
  eFloor := (792711958675/37778931862957161709568)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=583371,width:=116674,den:=549755813888,localDen:=906694364710971881029632,lowerC:=12144655291980,s:=[906694364691799147020288,-8040178778112,-412316860416],L:=[12144655291983,4857853789509,485784546214,-48,32],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor417Source.source.poly i) 583371 116674 549755813888
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor417Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 4) (CoreQuotient.fused G u 2 4) (((52/27) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (52/27) 2 4 WideAnchor417Source.data
    WideAnchor417Source.path_checked WideAnchor417Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor417Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 2) (CoreQuotient.fused G u 4 2) (((52/27) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (52/27) 4 2 WideAnchor417Source.data
    WideAnchor417Source.path_swapped WideAnchor417Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor417Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor417Cell031
