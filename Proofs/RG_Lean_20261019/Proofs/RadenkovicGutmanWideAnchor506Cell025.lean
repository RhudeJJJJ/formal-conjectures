/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor506Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor506Cell025
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1562959/4398046511104)
  b := (937775/2199023255552)
  s := [(549755813841/549755813888),(-147/4398046511104),(-9/2199023255552)]
  L := [(4610579007381/151115727451828646838272),(2766340324201/226673591177742970257408),(69158331049/56668397794435742564352),(5/14167099448608935641088),(-1/3541774862152233910272)]
  c := (1152644751845/37778931862957161709568)
  R := (-605323958498383/50000000000000)
  total := (-853805563/1000000000000000)
  k := 35
  n := 32
  sFloor := (2199023255281/4398046511104)
  nFloor := (1165776357881/151115727451828646838272)
  eFloor := (1629175538901/151115727451828646838272)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1562959,width:=312591,den:=4398046511104,localDen:=453347182355485940514816,lowerC:=13831737022140,s:=[453347182316728155635712,-15152644620288,-1855425871872],L:=[13831737022143,5532680648402,553266648392,160,-128],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor506Source.source.poly i) 1562959 312591 4398046511104
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor506Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 36) (CoreQuotient.fused G u 4 36) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 4 36 WideAnchor506Source.data
    WideAnchor506Source.path_checked WideAnchor506Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor506Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 36 4) (CoreQuotient.fused G u 36 4) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 36 4 WideAnchor506Source.data
    WideAnchor506Source.path_swapped WideAnchor506Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor506Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor506Cell025
