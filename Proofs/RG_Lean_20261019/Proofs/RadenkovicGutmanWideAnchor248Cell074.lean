/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor248Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor248Cell074
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1446879/536870912)
  b := (868127/268435456)
  s := [(549718583545/549755813888),(-59563733/2199023255552),(-372111/137438953472)]
  L := [(1193022030865/18014398509481984),(954365417139/36028797018963968),(143124677299/54043195528445952),(-247799/2251799813685248),(-18571/3377699720527872)]
  c := (1193022030865/18014398509481984)
  R := (-48112185122931/10000000000000)
  total := (-2542741932153/1000000000000000)
  k := 14
  n := 32
  sFloor := (2198808816671/4398046511104)
  nFloor := (709753868679/4503599627370496)
  eFloor := (1451613432115/18014398509481984)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1446879,width:=289375,den:=536870912,localDen:=108086391056891904,lowerC:=7158132185190,s:=[108079071273615360,-2927676604416,-292639997952],L:=[7158132185190,2863096251417,286249354598,-11894352,-594272],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor248Source.source.poly i) 1446879 289375 536870912
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor248Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 2) (CoreQuotient.fused G u 0 2) (((48/25) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (48/25) 0 2 WideAnchor248Source.data
    WideAnchor248Source.path_checked WideAnchor248Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor248Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 0) (CoreQuotient.fused G u 2 0) (((48/25) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (48/25) 2 0 WideAnchor248Source.data
    WideAnchor248Source.path_swapped WideAnchor248Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor248Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor248Cell074
