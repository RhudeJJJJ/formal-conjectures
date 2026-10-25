/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor393Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor393Cell076
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (130219/33554432)
  b := (625051/134217728)
  s := [(2198570361045/2199023255552),(-362229971/4398046511104),(-18087897/2199023255552)]
  L := [(102753565928009939907993937/633825300114114700748351602688),(1752002896591/27021597764222976),(87549398423/13510798882111488),(-79003/105553116266496),(-31529/844424930131968)]
  c := (1460215996871/9007199254740992)
  R := (-3409060580433/781250000000)
  total := (-828532124129/250000000000000)
  k := 13
  n := 32
  sFloor := (1099185579081/2199023255552)
  nFloor := (798757564649/2251799813685248)
  eFloor := (253711186411/1125899906842624)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=520876,width:=104175,den:=134217728,localDen:=1901475900342344102245054808064,lowerC:=308260697783844044676268032,s:=[1901084286480015140102539837440,-156608521192130454944219136,-15640444068310255197487104],L:=[308260697784029819723981811,123286243628738394323943424,12321482441072934066847744,-1423191525444605181952,-70996996325682184192],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor393Source.source.poly i) 520876 104175 134217728
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor393Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 2) (CoreQuotient.fused G u 2 2) (((56/29) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (56/29) 2 2 WideAnchor393Source.data
    WideAnchor393Source.path_checked WideAnchor393Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor393Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 2) (CoreQuotient.fused G u 2 2) (((56/29) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (56/29) 2 2 WideAnchor393Source.data
    WideAnchor393Source.path_swapped WideAnchor393Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor393Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor393Cell076
