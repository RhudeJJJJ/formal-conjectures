/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor239Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor239Cell133
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (518331/4096)
  b := 128
  s := [(4550556842977/18446744073709551616),(-156840209079/18446744073709551616),(1751850149/9223372036854775808)]
  L := [(1238094011912614243837854591/1237940039285380274899124224),(-1568301/549755813888),(53955/1099511627776),(-13/17179869184),(1/68719476736)]
  c := (1099645299477/1099511627776)
  R := (6078315717/100000000000000)
  total := (17882685237/200000000000000)
  k := 0
  n := 32
  sFloor := (1099305083549/9223372036854775808)
  nFloor := 2598642415289470385132990011347490745712757024695180593456626880630349038214596337030256304133085073506304
  eFloor := 2598317959346820411396838425597623472820450431316743268517528905642550272950749687254799504380920353259520
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=518331,width:=5957,den:=4096,localDen:=1237940039285380274899124224,lowerC:=1238090540241083669988507648,s:=[305382700299612848128,-10525368260814176256,235129346795241472],L:=[1238094011912614243837854591,-3531499899602388123648,60747929473693777920,-936748722493063168,18014398509481984],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor239Source.source.poly i) 518331 5957 4096
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor239Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 21) (CoreQuotient.fused G u 0 21) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 21 WideAnchor239Source.data
    WideAnchor239Source.path_checked WideAnchor239Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor239Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 21 0) (CoreQuotient.fused G u 21 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 21 0 WideAnchor239Source.data
    WideAnchor239Source.path_swapped WideAnchor239Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor239Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor239Cell133
