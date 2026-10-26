/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor278Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor278Cell060
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (901543/4294967296)
  b := (1081851/4294967296)
  s := [(549755307765/549755813888),(-1619585/4398046511104),(-80979/2199023255552)]
  L := [(1688984172807/2305843009213693952),(2026772584301/6917529027641081856),(101337956267/3458764513820540928),(-2099/108086391056891904),(-209/216172782113783808)]
  c := (1688984172807/2305843009213693952)
  R := (-706341481559707/100000000000000)
  total := (-292595837823/1000000000000000)
  k := 21
  n := 32
  sFloor := (34359692817/68719476736)
  nFloor := (194550935281/144115188075855872)
  eFloor := (489050680699/576460752303423488)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=901543,width:=180308,den:=4294967296,localDen:=6917529027641081856,lowerC:=5066952518421,s:=[6917522659139911680,-2547386941440,-254737907712],L:=[5066952518421,2026772584301,202675912534,-134336,-6688],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor278Source.source.poly i) 901543 180308 4294967296
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor278Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 6) (CoreQuotient.fused G u 0 6) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 6 WideAnchor278Source.data
    WideAnchor278Source.path_checked WideAnchor278Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor278Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 6 0) (CoreQuotient.fused G u 6 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 6 0 WideAnchor278Source.data
    WideAnchor278Source.path_swapped WideAnchor278Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor278Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor278Cell060
