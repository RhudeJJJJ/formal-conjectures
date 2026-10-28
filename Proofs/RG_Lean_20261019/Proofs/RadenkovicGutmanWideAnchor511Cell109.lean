/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor511Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor511Cell109
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1669171/1048576)
  b := (500751/262144)
  s := [(3397300757549/70368744177664),(-1184780700775/70368744177664),(102625728295/35184372088832)]
  L := [(88073383301708703019/73786976294838206464),(-19209931033/13194139533312),(-19563739175/2199023255552),(1983532171/824633720832),(-42040453/137438953472)]
  c := (651660685115/549755813888)
  R := (1700497999661/20000000000000)
  total := (27752237141423/1000000000000000)
  k := 0
  n := 32
  sFloor := (604442878341/35184372088832)
  nFloor := 18170823775787440949054981275648
  eFloor := 13821105055856494089829999443968
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1669171,width:=333833,den:=1048576,localDen:=221360928884514619392,lowerC:=262393249749176156160,s:=[10686984117443100672,-3726997824287539200,645665254035947520],L:=[264220149905126109057,-322289162285744128,-1969350467439820800,532450362813054976,-67710889029009408],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor511Source.source.poly i) 1669171 333833 1048576
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor511Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 41) (CoreQuotient.fused G u 4 41) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 4 41 WideAnchor511Source.data
    WideAnchor511Source.path_checked WideAnchor511Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor511Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 41 4) (CoreQuotient.fused G u 41 4) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 41 4 WideAnchor511Source.data
    WideAnchor511Source.path_swapped WideAnchor511Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor511Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor511Cell109
