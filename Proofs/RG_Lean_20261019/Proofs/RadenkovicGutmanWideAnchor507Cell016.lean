/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor507Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor507Cell016
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (302913/4398046511104)
  b := (726991/8796093022208)
  s := [(549755813885/549755813888),(-9/4398046511104),(-1/2199023255552)]
  L := [(3472120836833/1208925819614629174706176),(520817265841/453347182355485940514816),(52081640593/453347182355485940514816),(1/14167099448608935641088),(-1/28334198897217871282176)]
  c := (108503776151/37778931862957161709568)
  R := (-1328799386471979/100000000000000)
  total := (-181749181/1000000000000000)
  k := 39
  n := 32
  sFloor := (1099511627767/2199023255552)
  nFloor := (540497600043/1208925819614629174706176)
  eFloor := (1023892950981/2417851639229258349412352)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=605826,width:=121165,den:=8796093022208,localDen:=3626777458843887524118528,lowerC:=10416362510496,s:=[3626777458824096314818560,-7421703487488,-1649267441664],L:=[10416362510499,4166538126728,416653124744,256,-128],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor507Source.source.poly i) 605826 121165 8796093022208
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor507Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 37) (CoreQuotient.fused G u 4 37) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 4 37 WideAnchor507Source.data
    WideAnchor507Source.path_checked WideAnchor507Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor507Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 37 4) (CoreQuotient.fused G u 37 4) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 37 4 WideAnchor507Source.data
    WideAnchor507Source.path_swapped WideAnchor507Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor507Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor507Cell016
