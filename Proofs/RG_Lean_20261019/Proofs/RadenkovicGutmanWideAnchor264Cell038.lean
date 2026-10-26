/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor264Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor264Cell038
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1045159/274877906944)
  b := (627095/137438953472)
  s := [(4398046447795/4398046511104),(-25321/4398046511104),(-1267/2199023255552)]
  L := [(3918329600859/590295810358705651712),(1567325796075/590295810358705651712),(235097942141/885443715538058477568),(-229/36893488147419103232),(-17/55340232221128654848)]
  c := (1959164800429/295147905179352825856)
  R := (-188304689019513/20000000000000)
  total := (-7088539691/1000000000000000)
  k := 28
  n := 32
  sFloor := (1099511604985/2199023255552)
  nFloor := (671889487443/590295810358705651712)
  eFloor := (364256613183/295147905179352825856)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1045159,width:=209031,den:=274877906944,localDen:=1770887431076116955136,lowerC:=11754988802574,s:=[1770887405584546529280,-10195581272064,-1020323168256],L:=[11754988802577,4701977388225,470195884282,-10992,-544],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor264Source.source.poly i) 1045159 209031 274877906944
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor264Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 40) (CoreQuotient.fused G u 0 40) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 40 WideAnchor264Source.data
    WideAnchor264Source.path_checked WideAnchor264Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor264Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 40 0) (CoreQuotient.fused G u 40 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 40 0 WideAnchor264Source.data
    WideAnchor264Source.path_swapped WideAnchor264Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor264Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor264Cell038
