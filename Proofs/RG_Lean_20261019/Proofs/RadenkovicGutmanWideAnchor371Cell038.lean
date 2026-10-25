/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor371Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor371Cell038
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1045159/274877906944)
  b := (627095/137438953472)
  s := [(2199023252863/2199023255552),(-1075/2199023255552),(-27/549755813888)]
  L := [(2872954095089/9444732965739290427392),(861882928741/7083549724304467820544),(172375925053/14167099448608935641088),(-11/885443715538058477568),(-1/885443715538058477568)]
  c := (179559630943/590295810358705651712)
  R := (-68479319572247/6250000000000)
  total := (-4130370479/500000000000000)
  k := 32
  n := 32
  sFloor := (68719476615/137438953472)
  nFloor := (1988099718993/9444732965739290427392)
  eFloor := (499423621941/1180591620717411303424)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1045159,width:=209031,den:=274877906944,localDen:=28334198897217871282176,lowerC:=8618862285264,s:=[28334198862570370105344,-13851269529600,-1391569403904],L:=[8618862285267,3447531714964,344751850106,-352,-32],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor371Source.source.poly i) 1045159 209031 274877906944
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor371Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 10) (CoreQuotient.fused G u 2 10) (((15/8) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (15/8) 2 10 WideAnchor371Source.data
    WideAnchor371Source.path_checked WideAnchor371Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor371Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 10 2) (CoreQuotient.fused G u 10 2) (((15/8) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (15/8) 10 2 WideAnchor371Source.data
    WideAnchor371Source.path_swapped WideAnchor371Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor371Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor371Cell038
