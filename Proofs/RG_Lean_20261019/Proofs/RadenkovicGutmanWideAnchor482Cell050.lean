/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor482Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor482Cell050
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (582419/17179869184)
  b := (1397805/34359738368)
  s := [(2199023015417/2199023255552),(-96053/2199023255552),(-4803/1099511627776)]
  L := [(3487585471051/147573952589676412928),(1395030487871/147573952589676412928),(69751323233/73786976294838206464),(-541/9223372036854775808),(-13/4611686018427387904)]
  c := (1743792735525/73786976294838206464)
  R := (-878031516345633/100000000000000)
  total := (-3681065513/62500000000000)
  k := 26
  n := 32
  sFloor := (1099511454879/2199023255552)
  nFloor := (171043950073/9223372036854775808)
  eFloor := (395173544627/9223372036854775808)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1164838,width:=232967,den:=34359738368,localDen:=147573952589676412928,lowerC:=3487585471050,s:=[147573936474489356288,-6446007713792,-644647747584],L:=[3487585471051,1395030487871,139502646466,-8656,-416],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor482Source.source.poly i) 1164838 232967 34359738368
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor482Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 12) (CoreQuotient.fused G u 4 12) (((40/21) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (40/21) 4 12 WideAnchor482Source.data
    WideAnchor482Source.path_checked WideAnchor482Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor482Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 12 4) (CoreQuotient.fused G u 12 4) (((40/21) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (40/21) 12 4 WideAnchor482Source.data
    WideAnchor482Source.path_swapped WideAnchor482Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor482Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor482Cell050
