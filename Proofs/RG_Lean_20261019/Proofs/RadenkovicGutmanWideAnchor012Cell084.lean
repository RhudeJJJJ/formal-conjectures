/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor012Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor012Cell084
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (139979/8388608)
  b := (671899/33554432)
  s := [(3800910906485/17592186044416),(-116796285429/4398046511104),(11192031587/2199023255552)]
  L := [(274941771777061163053/295147905179352825856),(216389384909/4398046511104),(-80658966473/6597069766656),(502477907/274877906944),(-82646359/412316860416)]
  c := (1024237915043/1099511627776)
  R := (-221616462279/6250000000000)
  total := (-81353760017/1000000000000000)
  k := 1
  n := 32
  sFloor := (427907752183/4398046511104)
  nFloor := (491276339561/17592186044416)
  eFloor := (679963407321/35184372088832)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=559916,width:=111983,den:=33554432,localDen:=885443715538058477568,lowerC:=824825315331170893824,s:=[191306109824563937280,-23514198103679827968,4506507153934123008],L:=[824825315331183489159,43564937408705200128,-10825863222834233344,1618594633145647104,-177481704519237632],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor012Source.source.poly i) 559916 111983 33554432
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor012Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 21) (CoreQuotient.fused G u 9 21) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 21 WideAnchor012Source.data
    WideAnchor012Source.path_checked WideAnchor012Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor012Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 21 9) (CoreQuotient.fused G u 21 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 21 9 WideAnchor012Source.data
    WideAnchor012Source.path_swapped WideAnchor012Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor012Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor012Cell084
