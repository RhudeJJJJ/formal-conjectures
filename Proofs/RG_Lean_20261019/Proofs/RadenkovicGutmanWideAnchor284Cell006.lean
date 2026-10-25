/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor284Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor284Cell006
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (195689/17592186044416)
  b := (939307/70368744177664)
  s := [(4398046511103/4398046511104)]
  L := [(416306505051239652048459487/174224571863520493293247799005065324265472),(7099276442753/7427640235712281649394745344),(354963368573/3713820117856140824697372672),(19/464227514732017603087171584),(-5/232113757366008801543585792)]
  c := (1479017815069/618970019642690137449562112)
  R := (-1683384986245147/100000000000000)
  total := (-18621067/500000000000000)
  k := 49
  n := 32
  sFloor := (2199023255551/4398046511104)
  nFloor := (82426705743/38685626227668133590597632)
  eFloor := (102791593461/38685626227668133590597632)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=782756,width:=156551,den:=70368744177664,localDen:=522673715590561479879743397015195972796416,lowerC:=1248919515153576293189025792,s:=[522673715590442637635972000508805656870912],L:=[1248919515153718956145378461,499567167846602362157268992,49956652951110588452306944,21392098230009856,-11258999068426240],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor284Source.source.poly i) 782756 156551 70368744177664
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor284Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 8) (CoreQuotient.fused G u 0 8) (((13/7) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (13/7) 0 8 WideAnchor284Source.data
    WideAnchor284Source.path_checked WideAnchor284Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor284Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 8 0) (CoreQuotient.fused G u 8 0) (((13/7) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (13/7) 8 0 WideAnchor284Source.data
    WideAnchor284Source.path_swapped WideAnchor284Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor284Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor284Cell006
