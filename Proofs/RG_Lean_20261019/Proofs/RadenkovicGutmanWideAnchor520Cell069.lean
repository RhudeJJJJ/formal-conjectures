/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor520Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor520Cell069
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (581469/536870912)
  b := (1395525/1073741824)
  s := [(4229926755167/4398046511104),(-31736808231/2199023255552),(-1120872809/1099511627776)]
  L := [(384438521552543738881/18889465931478580854784),(2200460756659/281474976710656),(278154874177/422212465065984),(-392981423/17592186044416),(-11619049/26388279066624)]
  c := (716072547347/35184372088832)
  R := (-3894575803313/2000000000000)
  total := (-628757983/1562500000000)
  k := 6
  n := 32
  sFloor := (1040492411867/2199023255552)
  nFloor := (286716284365/9007199254740992)
  eFloor := (549016114667/18014398509481984)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1162938,width:=232587,den:=1073741824,localDen:=56668397794435742564352,lowerC:=1153315564657041211392,s:=[54502191233752992055296,-817851320589411680256,-57769344691567853568],L:=[1153315564657631216643,443011264967897776128,37333315244162809856,-1265881769790406656,-24951717732810752],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor520Source.source.poly i) 1162938 232587 1073741824
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor520Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 5) (CoreQuotient.fused G u 4 5) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 4 5 WideAnchor520Source.data
    WideAnchor520Source.path_checked WideAnchor520Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor520Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 5 4) (CoreQuotient.fused G u 5 4) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 5 4 WideAnchor520Source.data
    WideAnchor520Source.path_swapped WideAnchor520Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor520Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor520Cell069
