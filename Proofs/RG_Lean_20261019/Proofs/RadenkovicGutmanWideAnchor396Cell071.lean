/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor396Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor396Cell071
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (837315/536870912)
  b := (502389/268435456)
  s := [(2198954005077/2199023255552),(-55398499/4398046511104),(-2769403/2199023255552)]
  L := [(367378023873/18014398509481984),(587795390249/72057594037927936),(14693939987/18014398509481984),(-5905/562949953421312),(-295/562949953421312)]
  c := (367378023873/18014398509481984)
  R := (-135003631969499/25000000000000)
  total := (-103449925497/62500000000000)
  k := 16
  n := 32
  sFloor := (274865442053/549755813888)
  nFloor := (818441568045/18014398509481984)
  eFloor := (1263845661729/36028797018963968)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=837315,width:=167463,den:=536870912,localDen:=72057594037927936,lowerC:=1469512095492,s:=[72055324838363136,-907649007616,-90747797504],L:=[1469512095492,587795390249,58775759948,-755840,-37760],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor396Source.source.poly i) 837315 167463 536870912
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor396Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 2) (CoreQuotient.fused G u 2 2) (((17/9) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (17/9) 2 2 WideAnchor396Source.data
    WideAnchor396Source.path_checked WideAnchor396Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor396Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 2) (CoreQuotient.fused G u 2 2) (((17/9) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (17/9) 2 2 WideAnchor396Source.data
    WideAnchor396Source.path_swapped WideAnchor396Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor396Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor396Cell071
