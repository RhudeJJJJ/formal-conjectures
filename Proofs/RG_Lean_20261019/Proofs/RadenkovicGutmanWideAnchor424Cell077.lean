/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor424Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor424Cell077
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (625051/134217728)
  b := (750061/134217728)
  s := [(2197812609627/2199023255552),(-967843609/4398046511104),(-48205947/2199023255552)]
  L := [(11351860927346129019431315/39614081257132168796771975168),(2064303079737/18014398509481984),(103098015997/9007199254740992),(-2922243/1125899906842624),(-72689/562949953421312)]
  c := (1290557171085/4503599627370496)
  R := (-407877911624697/100000000000000)
  total := (-3711688760343/1000000000000000)
  k := 12
  n := 32
  sFloor := (2197280481875/4398046511104)
  nFloor := (283357448181/562949953421312)
  eFloor := (1089065602083/2251799813685248)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=625051,width:=125010,den:=134217728,localDen:=39614081257132168796771975168,lowerC:=11351860927341264560455680,s:=[39592272198985338358981459968,-8717560233690632057520128,-868401139784967518158848],L:=[11351860927346129019431315,4539450478849277583949824,453429869557350230130688,-102817285045984690176,-5115033645530218496],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor424Source.source.poly i) 625051 125010 134217728
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor424Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 6) (CoreQuotient.fused G u 2 6) (((48/25) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (48/25) 2 6 WideAnchor424Source.data
    WideAnchor424Source.path_checked WideAnchor424Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor424Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 6 2) (CoreQuotient.fused G u 6 2) (((48/25) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (48/25) 6 2 WideAnchor424Source.data
    WideAnchor424Source.path_swapped WideAnchor424Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor424Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor424Cell077
