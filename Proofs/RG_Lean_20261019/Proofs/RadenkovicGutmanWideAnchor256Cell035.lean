/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor256Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor256Cell035
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (302419/137438953472)
  b := (1451611/549755813888)
  s := [(2199023241233/2199023255552),(-2863/1099511627776),(-287/1099511627776)]
  L := [(4265891823383/1180591620717411303424),(5119065896083/3541774862152233910272),(85317690379/590295810358705651712),(-295/221360928884514619392),(-3/36893488147419103232)]
  c := (2132945911691/590295810358705651712)
  R := (-19438630261397/2000000000000)
  total := (-1058999879/250000000000000)
  k := 29
  n := 32
  sFloor := (2199023234933/4398046511104)
  nFloor := (116690747805/295147905179352825856)
  eFloor := (841114196379/2361183241434822606848)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1209676,width:=241935,den:=549755813888,localDen:=3541774862152233910272,lowerC:=12797675470146,s:=[3541774839089870143488,-9222368526336,-924491710464],L:=[12797675470149,5119065896083,511906142274,-4720,-288],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor256Source.source.poly i) 1209676 241935 549755813888
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor256Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 33) (CoreQuotient.fused G u 0 33) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 33 WideAnchor256Source.data
    WideAnchor256Source.path_checked WideAnchor256Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor256Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 33 0) (CoreQuotient.fused G u 33 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 33 0 WideAnchor256Source.data
    WideAnchor256Source.path_swapped WideAnchor256Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor256Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor256Cell035
