/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor274Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor274Cell061
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1081851/4294967296)
  b := (1298221/4294967296)
  s := [(4398042540679/4398046511104),(-794083/2199023255552),(-4963/137438953472)]
  L := [(897984260975707642493543249/1298074214633706907132624082305024),(1914165555205/6917529027641081856),(63805292119/2305843009213693952),(-6289/432345564227567616),(-103/144115188075855872)]
  c := (1595140483657/2305843009213693952)
  R := (-709199754417101/100000000000000)
  total := (-352555571303/1000000000000000)
  k := 21
  n := 32
  sFloor := (137438774803/274877906944)
  nFloor := (1650053033919/1152921504606846976)
  eFloor := (1076653744913/1152921504606846976)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1081851,width:=216370,den:=4294967296,localDen:=3894222643901120721397872246915072,lowerC:=2693952782925471736714493952,s:=[3894219128313256456202041448988672,-1406231603931216180085260288,-140622629126892295173439488],L:=[2693952782927122927480629747,1077579410143334573759528960,107757558679272766920720384,-56646276113066098688,-2783224569714966528],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor274Source.source.poly i) 1081851 216370 4294967296
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor274Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 4) (CoreQuotient.fused G u 0 4) (((44/23) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (44/23) 0 4 WideAnchor274Source.data
    WideAnchor274Source.path_checked WideAnchor274Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor274Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 0) (CoreQuotient.fused G u 4 0) (((44/23) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (44/23) 4 0 WideAnchor274Source.data
    WideAnchor274Source.path_swapped WideAnchor274Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor274Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor274Cell061
