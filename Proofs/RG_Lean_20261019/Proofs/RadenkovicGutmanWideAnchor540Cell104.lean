/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor540Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor540Cell104
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (670803/1048576)
  b := (1609927/2097152)
  s := [(5522509646829/35184372088832),(-465922163489/17592186044416),(4411217961/2199023255552)]
  L := [(148735698512734008501/147573952589676412928),(916351056713/13194139533312),(-18136924859/2199023255552),(-52306973/824633720832),(15113139/137438953472)]
  c := (34630228419/34359738368)
  R := (24504599147/6250000000000)
  total := (2490859609789/1000000000000000)
  k := 0
  n := 32
  sFloor := (582655600903/8796093022208)
  nFloor := (651371527807/32768)
  eFloor := (470927226035/32768)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1341606,width:=268321,den:=2097152,localDen:=442721857769029238784,lowerC:=446207095537844355072,s:=[69489252905200386048,-11725315164063399936,888095478657318912],L:=[446207095538202025503,30747639220604502016,-3651445271222550528,-28082092298469376,48682828308676608],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor540Source.source.poly i) 1341606 268321 2097152
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor540Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 5 18) (CoreQuotient.fused G u 5 18) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 5 18 WideAnchor540Source.data
    WideAnchor540Source.path_checked WideAnchor540Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor540Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 18 5) (CoreQuotient.fused G u 18 5) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 18 5 WideAnchor540Source.data
    WideAnchor540Source.path_swapped WideAnchor540Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor540Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor540Cell104
