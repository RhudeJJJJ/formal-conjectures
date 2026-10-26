/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor041Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor041Cell055
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (724621/8589934592)
  b := (869545/8589934592)
  s := [(4398041582197/4398046511104),(-985779/2199023255552),(-6161/137438953472)]
  L := [(5847045716879/18446744073709551616),(7016443599455/55340232221128654848),(350821380223/27670116110564327424),(-7883/3458764513820540928),(-199/1729382256910270464)]
  c := (1461761429219/4611686018427387904)
  R := (-187055773898559/25000000000000)
  total := (-62327062303/500000000000000)
  k := 22
  n := 32
  sFloor := (2199019706743/4398046511104)
  nFloor := (610452937229/2305843009213693952)
  eFloor := (1079186358843/2305843009213693952)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=724621,width:=144924,den:=8589934592,localDen:=55340232221128654848,lowerC:=17541137150628,s:=[55340170201125617664,-24807940816896,-2480746266624],L:=[17541137150637,7016443599455,701642760446,-126128,-6368],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor041Source.source.poly i) 724621 144924 8589934592
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor041Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 10 20) (CoreQuotient.fused G u 10 20) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 10 20 WideAnchor041Source.data
    WideAnchor041Source.path_checked WideAnchor041Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor041Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 20 10) (CoreQuotient.fused G u 20 10) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 20 10 WideAnchor041Source.data
    WideAnchor041Source.path_swapped WideAnchor041Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor041Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor041Cell055
