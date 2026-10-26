/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor527Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor527Cell004
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (543581/70368744177664)
  b := (652297/70368744177664)
  s := [(2199023255549/2199023255552),(-1/2199023255552)]
  L := [(91983232955/151115727451828646838272),(3532149647537/14507109835375550096474112),(176607157459/7253554917687775048237056),(1/226673591177742970257408),(-1/453347182355485940514816)]
  c := (91983232955/151115727451828646838272)
  R := (-351593259452739/25000000000000)
  total := (-21582911/1000000000000000)
  k := 41
  n := 32
  sFloor := (549755813887/1099511627776)
  nFloor := (582729878039/309485009821345068724781056)
  eFloor := (1106915262237/618970019642690137449562112)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=543581,width:=108716,den:=70368744177664,localDen:=14507109835375550096474112,lowerC:=8830390363680,s:=[14507109835355758887174144,-6597069766656],L:=[8830390363680,3532149647537,353214314918,64,-32],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor527Source.source.poly i) 543581 108716 70368744177664
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor527Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 7) (CoreQuotient.fused G u 4 7) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 4 7 WideAnchor527Source.data
    WideAnchor527Source.path_checked WideAnchor527Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor527Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 7 4) (CoreQuotient.fused G u 7 4) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 7 4 WideAnchor527Source.data
    WideAnchor527Source.path_swapped WideAnchor527Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor527Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor527Cell004
