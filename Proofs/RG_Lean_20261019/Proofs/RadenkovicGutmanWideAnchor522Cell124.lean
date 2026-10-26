/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor522Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor522Cell124
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1607301/65536)
  b := (241095/8192)
  s := [(4850946510313/144115188075855872),(-5540436640197/288230376151711744),(732455668091/144115188075855872)]
  L := [(1184412373603935479685/1180591620717411303424),(-8394063559/6597069766656),(408856423/1099511627776),(-37082927/412316860416),(951961/68719476736)]
  c := (1101996170591/1099511627776)
  R := (112856464631/100000000000000)
  total := (331172869591/50000000000000)
  k := 0
  n := 32
  sFloor := (21977998893/2251799813685248)
  nFloor := 1699881090777807921843887313179373469696
  eFloor := 1694283421297604565889668585469081812992
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1607301,width:=321459,den:=65536,localDen:=3541774862152233910272,lowerC:=3549778134754186493952,s:=[119216861437452288,-68080885434740736,18000830499004416],L:=[3553237120811806439055,-4506528558306295808,1317018724158406656,-318539917409910784,49063696344809472],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor522Source.source.poly i) 1607301 321459 65536
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor522Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 6) (CoreQuotient.fused G u 4 6) (((23/12) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (23/12) 4 6 WideAnchor522Source.data
    WideAnchor522Source.path_checked WideAnchor522Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor522Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 6 4) (CoreQuotient.fused G u 6 4) (((23/12) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (23/12) 6 4 WideAnchor522Source.data
    WideAnchor522Source.path_swapped WideAnchor522Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor522Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor522Cell124
