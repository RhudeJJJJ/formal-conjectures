/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor572Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor572Cell037
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (435483/137438953472)
  b := (1045159/274877906944)
  s := [(4398046508189/4398046511104),(-583/2199023255552),(-29/1099511627776)]
  L := [(163323459818289078353873151/1329227995784915872903807060280344576),(348144494309/7083549724304467820544),(69628819013/14167099448608935641088),(23/3541774862152233910272),(-1/442721857769029238784)]
  c := (580241489765/4722366482869645213696)
  R := (-1140994339240993/100000000000000)
  total := (-71712011/10000000000000)
  k := 33
  n := 32
  sFloor := (2199023253453/4398046511104)
  nFloor := (1312861126435/9444732965739290427392)
  eFloor := (884996007735/2361183241434822606848)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=870966,width:=174193,den:=274877906944,localDen:=3987683987354747618711421180841033728,lowerC:=489970379454479150371307520,s:=[3987683984711733545578938147639656448,-1057205629252993213280550912,-105176546306472738199437312],L:=[489970379454867235061619453,195987926855137770663313408,19598770210074656692502528,25895697857380352,-9007199254740992],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor572Source.source.poly i) 870966 174193 274877906944
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
end Gebendorfer.RadenkovicGutman.WideAnchor572Cell037
