/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor542Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor542Cell055
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (724621/8589934592)
  b := (869545/8589934592)
  s := [(4396808294189/4398046511104),(-30942603/274877906944),(-12348675/1099511627776)]
  L := [(23106730250568663560394979/158456325028528675187087900672),(3151397374837/54043195528445952),(52462200303/9007199254740992),(-4573237/3377699720527872),(-37927/562949953421312)]
  c := (164183193267/1125899906842624)
  R := (-441655517726349/100000000000000)
  total := (-583459821/8000000000000)
  k := 13
  n := 32
  sFloor := (274766488615/549755813888)
  nFloor := (982116927179/2305843009213693952)
  eFloor := (237051303781/576460752303423488)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=724621,width:=144924,den:=8589934592,localDen:=475368975085586025561263702016,lowerC:=69320190751664936979529728,s:=[475235140687898077278404345856,-53511588610818505590177792,-5338894860337858530508800],L:=[69320190751705990681184937,27719984459008344741380096,2768774364089380339974144,-643625889033655156736,-32026504325115150336],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor542Source.source.poly i) 724621 144924 8589934592
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor542Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 5 20) (CoreQuotient.fused G u 5 20) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 5 20 WideAnchor542Source.data
    WideAnchor542Source.path_checked WideAnchor542Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor542Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 20 5) (CoreQuotient.fused G u 20 5) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 20 5 WideAnchor542Source.data
    WideAnchor542Source.path_swapped WideAnchor542Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor542Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor542Cell055
