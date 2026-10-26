/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor508Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor508Cell103
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1118005/2097152)
  b := (670803/1048576)
  s := [(6962148993887/35184372088832),(-320523317511/8796093022208),(37772618265/8796093022208)]
  L := [(68969208703492606527/73786976294838206464),(67139396093/824633720832),(-5976672749/549755813888),(428809211/412316860416),(-1514453/17179869184)]
  c := (2055442592605/2199023255552)
  R := (-211006527313/6250000000000)
  total := (-190518120551/125000000000000)
  k := 1
  n := 32
  sFloor := (1457786549225/17592186044416)
  nFloor := (1530427521897/64)
  eFloor := (548197078117/32)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1118005,width:=223601,den:=2097152,localDen:=221360928884514619392,lowerC:=206907626110404526080,s:=[43802054060484329472,-8066233396377944064,950579063276175360],L:=[206907626110477819581,18022594405789073408,-2406526312110882816,230215192183570432,-19513578318987264],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor508Source.source.poly i) 1118005 223601 2097152
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor508Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 38) (CoreQuotient.fused G u 4 38) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 4 38 WideAnchor508Source.data
    WideAnchor508Source.path_checked WideAnchor508Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor508Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 38 4) (CoreQuotient.fused G u 38 4) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 38 4 WideAnchor508Source.data
    WideAnchor508Source.path_swapped WideAnchor508Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor508Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor508Cell103
