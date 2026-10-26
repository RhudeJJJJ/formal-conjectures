/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor572Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor572Cell041
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (112877/17179869184)
  b := (1083619/137438953472)
  s := [(4398046498573/4398046511104),(-5011/4398046511104),(-251/2199023255552)]
  L := [(1404517149339387086074485289/2658455991569831745807614120560689152),(748476265979/3541774862152233910272),(49898362907/2361183241434822606848),(11/442721857769029238784),(1/147573952589676412928)]
  c := (1247461822141/2361183241434822606848)
  R := (-534032943978663/50000000000000)
  total := (-2782370851/200000000000000)
  k := 31
  n := 32
  sFloor := (1099511623265/2199023255552)
  nFloor := (352815200573/590295810358705651712)
  eFloor := (951326949727/590295810358705651712)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=903016,width:=180603,den:=137438953472,localDen:=7975367974709495237422842361682067456,lowerC:=4213551448014845667497213952,s:=[7975367951985921069036465079317430272,-9086890923133360191678971904,-910321142169815768553750528],L:=[4213551448018161258223455867,1685418716279342326236577792,168541686445772234664443904,198158383604301824,54043195528445952],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor572Source.source.poly i) 903016 180603 137438953472
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor572Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 6 10) (CoreQuotient.fused G u 6 10) (((21/11) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (21/11) 6 10 WideAnchor572Source.data
    WideAnchor572Source.path_checked WideAnchor572Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor572Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 10 6) (CoreQuotient.fused G u 10 6) (((21/11) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (21/11) 10 6 WideAnchor572Source.data
    WideAnchor572Source.path_swapped WideAnchor572Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor572Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor572Cell041
