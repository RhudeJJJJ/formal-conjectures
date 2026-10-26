/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor263Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor263Cell054
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (603851/8589934592)
  b := (724621/8589934592)
  s := [(1099505775535/1099511627776),(-4681725/2199023255552),(-117035/549755813888)]
  L := [(3397112030623/1152921504606846976),(4076485353961/3458764513820540928),(25476932987/216172782113783808),(-105827/108086391056891904),(-2645/54043195528445952)]
  c := (1698556015311/576460752303423488)
  R := (-318372101243781/50000000000000)
  total := (-44102550823/500000000000000)
  k := 19
  n := 32
  sFloor := (2199006401205/4398046511104)
  nFloor := (1076855088071/2305843009213693952)
  eFloor := (972614307633/2305843009213693952)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=603851,width:=120770,den:=8589934592,localDen:=3458764513820540928,lowerC:=10191336091866,s:=[3458746104262164480,-7363716710400,-736320552960],L:=[10191336091869,4076485353961,407630927792,-3386464,-169280],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor263Source.source.poly i) 603851 120770 8589934592
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor263Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 39) (CoreQuotient.fused G u 0 39) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 39 WideAnchor263Source.data
    WideAnchor263Source.path_checked WideAnchor263Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor263Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 39 0) (CoreQuotient.fused G u 39 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 39 0 WideAnchor263Source.data
    WideAnchor263Source.path_swapped WideAnchor263Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor263Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor263Cell054
