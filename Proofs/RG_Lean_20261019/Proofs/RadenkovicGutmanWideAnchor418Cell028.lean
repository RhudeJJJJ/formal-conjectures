/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor418Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor418Cell028
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (337599/549755813888)
  b := (1620475/2199023255552)
  s := [(4398046511073/4398046511104),(-11/4398046511104),(-1/2199023255552)]
  L := [(581728210263/151115727451828646838272),(1396146670741/906694364710971881029632),(69807281861/453347182355485940514816),(-1/14167099448608935641088),(1/28334198897217871282176)]
  c := (581728210263/151115727451828646838272)
  R := (-328538296502353/25000000000000)
  total := (-100156303/62500000000000)
  k := 38
  n := 32
  sFloor := (1099511627765/2199023255552)
  nFloor := (1159706740259/151115727451828646838272)
  eFloor := (260885307613/37778931862957161709568)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1350396,width:=270079,den:=2199023255552,localDen:=906694364710971881029632,lowerC:=3490369261578,s:=[906694364704580969693184,-2267742732288,-412316860416],L:=[3490369261578,1396146670741,139614563722,-64,32],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor418Source.source.poly i) 1350396 270079 2199023255552
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor418Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 4) (CoreQuotient.fused G u 2 4) (((40/21) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (40/21) 2 4 WideAnchor418Source.data
    WideAnchor418Source.path_checked WideAnchor418Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor418Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 2) (CoreQuotient.fused G u 4 2) (((40/21) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (40/21) 4 2 WideAnchor418Source.data
    WideAnchor418Source.path_swapped WideAnchor418Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor418Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor418Cell028
