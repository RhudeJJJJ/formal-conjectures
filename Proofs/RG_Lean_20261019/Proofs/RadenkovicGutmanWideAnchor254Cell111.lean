/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor254Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor254Cell111
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (600901/262144)
  b := (721081/262144)
  s := [(3741606684565/140737488355328),(-1675021708855/140737488355328),(180225000951/70368744177664)]
  L := [(87861046160199630933/73786976294838206464),(-1896716381/51539607552),(493958331/274877906944),(97874815/103079215104),(-2114731/8589934592)]
  c := (1271517474481/1099511627776)
  R := (7267247125903/100000000000000)
  total := (9148151183787/250000000000000)
  k := 0
  n := 32
  sFloor := (606758744403/70368744177664)
  nFloor := 1255767206537259596215794794496
  eFloor := 999988273885095352007215022080
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=600901,width:=120180,den:=262144,localDen:=221360928884514619392,lowerC:=255990279805706698752,s:=[5885038456311644160,-2634581345076510720,566938831791587328],L:=[263583138480598892799,-8146334826182475776,397787789480951808,210184564763525120,-54496202909024256],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor254Source.source.poly i) 600901 120180 262144
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor254Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 31) (CoreQuotient.fused G u 0 31) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 31 WideAnchor254Source.data
    WideAnchor254Source.path_checked WideAnchor254Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor254Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 31 0) (CoreQuotient.fused G u 31 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 31 0 WideAnchor254Source.data
    WideAnchor254Source.path_swapped WideAnchor254Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor254Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor254Cell111
