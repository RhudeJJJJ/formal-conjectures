/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor377Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor377Cell009
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1352601/70368744177664)
  b := (1623121/70368744177664)
  s := [(4398046511103/4398046511104)]
  L := [(2768797437302380044673318763/174224571863520493293247799005065324265472),(92219411783/14507109835375550096474112),(147550949783/232113757366008801543585792),(-1/7253554917687775048237056),(1/14507109835375550096474112)]
  c := (614796533083/38685626227668133590597632)
  R := (-397161914226221/25000000000000)
  total := (-60712369/1000000000000000)
  k := 46
  n := 32
  sFloor := (2199023255551/4398046511104)
  nFloor := (630345083845/77371252455336267181195264)
  eFloor := (133209802821/9671406556917033397649408)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1352601,width:=270520,den:=70368744177664,localDen:=522673715590561479879743397015195972796416,lowerC:=8306392311903814849086357504,s:=[522673715590442637635972000508805656870912],L:=[8306392311907140134019956289,3322554468337961025031634944,332255201230440783815901184,-72057594037927936,36028797018963968],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor377Source.source.poly i) 1352601 270520 70368744177664
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor377Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 14) (CoreQuotient.fused G u 2 14) (((40/21) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (40/21) 2 14 WideAnchor377Source.data
    WideAnchor377Source.path_checked WideAnchor377Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor377Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 14 2) (CoreQuotient.fused G u 14 2) (((40/21) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (40/21) 14 2 WideAnchor377Source.data
    WideAnchor377Source.path_swapped WideAnchor377Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor377Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor377Cell009
