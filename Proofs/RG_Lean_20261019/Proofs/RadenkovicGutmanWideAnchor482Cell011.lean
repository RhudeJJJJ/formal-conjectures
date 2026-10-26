/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor482Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor482Cell011
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (60867/2199023255552)
  b := (584323/17592186044416)
  s := [(4398046511103/4398046511104)]
  L := [(85772367404179935917029987/5444517870735015415413993718908291383296),(1462675378273/232113757366008801543585792),(146267237425/232113757366008801543585792),(1/7253554917687775048237056),(-1/14507109835375550096474112)]
  c := (1218898651759/77371252455336267181195264)
  R := (-158908443528303/10000000000000)
  total := (-21862453/250000000000000)
  k := 46
  n := 32
  sFloor := (2199023255551/4398046511104)
  nFloor := (119558465623/9671406556917033397649408)
  eFloor := (1104893754785/38685626227668133590597632)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=486936,width:=97387,den:=17592186044416,localDen:=16333553612205046246241981156724874149888,lowerC:=257317102212385892286332928,s:=[16333553612201332426124125015900176777216],L:=[257317102212539807751089961,102926629508660657517494272,10292641811933466669875200,2251799813685248,-1125899906842624],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor482Source.source.poly i) 486936 97387 17592186044416
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor482Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 12) (CoreQuotient.fused G u 4 12) (((40/21) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (40/21) 4 12 WideAnchor482Source.data
    WideAnchor482Source.path_checked WideAnchor482Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor482Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 12 4) (CoreQuotient.fused G u 12 4) (((40/21) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (40/21) 12 4 WideAnchor482Source.data
    WideAnchor482Source.path_swapped WideAnchor482Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor482Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor482Cell011
