/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor025Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor025Cell125
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (241095/8192)
  b := (144657/4096)
  s := [(2813490889795/144115188075855872),(-402208931383/36028797018963968),(212928021769/72057594037927936)]
  L := [(9244218666413735695/9223372036854775808),(-5885945809/6597069766656),(36006871/137438953472),(-3281671/51539607552),(338235/34359738368)]
  c := (1101244618213/1099511627776)
  R := (78745240339/100000000000000)
  total := (138740982867/25000000000000)
  k := 0
  n := 32
  sFloor := (1630511207801/288230376151711744)
  nFloor := 2600814918510435304671596233214374106456638341986103785937663879601508488709847988059784251989763217271560958596361168423839835004476588032
  eFloor := 2594848483464882121787934972026714381645632053982464453470233890791150363145597308048162936584595079737871469321556087157008687644482207744
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=241095,width:=48219,den:=8192,localDen:=27670116110564327424,lowerC:=27713728242895552512,s:=[540190250840640,-308896459302144,81764360359296],L:=[27732655999241207085,-24687446050471936,7249140627013632,-1761833702653952,272382799380480],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor025Source.source.poly i) 241095 48219 8192
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor025Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 34) (CoreQuotient.fused G u 9 34) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 34 WideAnchor025Source.data
    WideAnchor025Source.path_checked WideAnchor025Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor025Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 34 9) (CoreQuotient.fused G u 34 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 34 9 WideAnchor025Source.data
    WideAnchor025Source.path_swapped WideAnchor025Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor025Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor025Cell125
