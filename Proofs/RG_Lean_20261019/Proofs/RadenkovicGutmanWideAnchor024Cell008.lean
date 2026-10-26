/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor024Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor024Cell008
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (4403/274877906944)
  b := (1352601/70368744177664)
  s := [(274877906939/274877906944),(-33/4398046511104),(-1/2199023255552)]
  L := [(4050994942545/302231454903657293676544),(1620393664223/302231454903657293676544),(243058402829/453347182355485940514816),(-9/18889465931478580854784),(7/28334198897217871282176)]
  c := (253187183909/18889465931478580854784)
  R := (-1251774822598687/100000000000000)
  total := (-9950381/250000000000000)
  k := 37
  n := 32
  sFloor := (1099511627747/2199023255552)
  nFloor := (1316612843155/38685626227668133590597632)
  eFloor := (1772797269719/77371252455336267181195264)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1127168,width:=225433,den:=70368744177664,localDen:=906694364710971881029632,lowerC:=12152984827632,s:=[906694364694479206612992,-6803228196864,-412316860416],L:=[12152984827635,4861180992669,486116805658,-432,224],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor024Source.source.poly i) 1127168 225433 70368744177664
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor024Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 33) (CoreQuotient.fused G u 9 33) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 33 WideAnchor024Source.data
    WideAnchor024Source.path_checked WideAnchor024Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor024Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 33 9) (CoreQuotient.fused G u 33 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 33 9 WideAnchor024Source.data
    WideAnchor024Source.path_swapped WideAnchor024Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor024Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor024Cell008
