/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor035Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor035Cell082
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (388831/33554432)
  b := (466597/33554432)
  s := [(8679834393709/8796093022208),(-45683952237/8796093022208),(-2064553077/4398046511104)]
  L := [(10939818961861006019375/2417851639229258349412352),(47692305125/26388279066624),(25286174423/140737488355328),(-24759401/105553116266496),(-83579/4398046511104)]
  c := (1273562545173/281474976710656)
  R := (-269911271195001/100000000000000)
  total := (-1509648327041/250000000000000)
  k := 8
  n := 32
  sFloor := (2157505333829/4398046511104)
  nFloor := (88445515457/17592186044416)
  eFloor := (1040327983921/140737488355328)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=388831,width:=77766,den:=33554432,localDen:=7253554917687775048237056,lowerC:=32819456885571345973248,s:=[7157684132289819483045888,-37672527515508679901184,-3405000171483329200128],L:=[32819456885583018058125,13109561010094604288000,1303239506252840042496,-1701453081016795136,-137844123506835456],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor035Source.source.poly i) 388831 77766 33554432
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor035Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 10 14) (CoreQuotient.fused G u 10 14) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 10 14 WideAnchor035Source.data
    WideAnchor035Source.path_checked WideAnchor035Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor035Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 14 10) (CoreQuotient.fused G u 14 10) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 14 10 WideAnchor035Source.data
    WideAnchor035Source.path_swapped WideAnchor035Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor035Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor035Cell082
