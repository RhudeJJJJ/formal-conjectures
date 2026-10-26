/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor522Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor522Cell025
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1562959/4398046511104)
  b := (937775/2199023255552)
  s := [(2199023255543/2199023255552),(-5/4398046511104),(-1/2199023255552)]
  L := [(3756480637487/2417851639229258349412352),(2253882614213/3626777458843887524118528),(28173460585/453347182355485940514816),(-1/28334198897217871282176),(1/56668397794435742564352)]
  c := (1878240318743/1208925819614629174706176)
  R := (-3398802248877/250000000000)
  total := (-959616983/1000000000000000)
  k := 40
  n := 32
  sFloor := (2199023255539/4398046511104)
  nFloor := (791719783077/302231454903657293676544)
  eFloor := (992268131077/302231454903657293676544)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1562959,width:=312591,den:=4398046511104,localDen:=7253554917687775048237056,lowerC:=11269441912458,s:=[7253554917658088234287104,-8246337208320,-3298534883328],L:=[11269441912461,4507765228426,450775369360,-256,128],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor522Source.source.poly i) 1562959 312591 4398046511104
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor522Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 6) (CoreQuotient.fused G u 4 6) (((23/12) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (23/12) 4 6 WideAnchor522Source.data
    WideAnchor522Source.path_checked WideAnchor522Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor522Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 6 4) (CoreQuotient.fused G u 6 4) (((23/12) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (23/12) 6 4 WideAnchor522Source.data
    WideAnchor522Source.path_swapped WideAnchor522Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor522Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor522Cell025
