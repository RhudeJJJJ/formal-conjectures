/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor012Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor012Cell068
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (969115/1073741824)
  b := (581469/536870912)
  s := [(1054697133325/1099511627776),(-67443019153/4398046511104),(-2327525425/2199023255552)]
  L := [(573553946708524728089/18889465931478580854784),(4912922826121/422212465065984),(68286794981/70368744177664),(-920637517/26388279066624),(-2768517/4398046511104)]
  c := (2136654953317/70368744177664)
  R := (-87362692241161/50000000000000)
  total := (-299271865971/1000000000000000)
  k := 6
  n := 32
  sFloor := (64792038489/137438953472)
  nFloor := (704462119921/9007199254740992)
  eFloor := (965303224569/18014398509481984)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=969115,width:=193823,den:=1073741824,localDen:=56668397794435742564352,lowerC:=1720661840124922822656,s:=[54358676337789920870400,-868996684816909860864,-59979873485901004800],L:=[1720661840125574184267,659401339561299673088,54991790848509739008,-1977054013492822016,-35672069920260096],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor012Source.source.poly i) 969115 193823 1073741824
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
end Gebendorfer.RadenkovicGutman.WideAnchor012Cell068
