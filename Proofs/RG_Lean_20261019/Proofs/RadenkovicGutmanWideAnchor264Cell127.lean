/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor264Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor264Cell127
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1388707/32768)
  b := (104153/2048)
  s := [(7560388427893/1152921504606846976),(-2165499380913/576460752303423488),(35878939011/36028797018963968)]
  L := [(2363777633664510156759/2361183241434822606848),(-1918069259/4398046511104),(283399711/2199023255552),(-8664813/274877906944),(673041/137438953472)]
  c := (550176321709/549755813888)
  R := (38230344207/100000000000000)
  total := (3883446372579/1000000000000000)
  k := 0
  n := 32
  sFloor := (2188757857209/1152921504606846976)
  nFloor := 325407822996401880449936952782840842970849945064844006698426590707751404801414374188749090824311723073354748582246522815500075041749130920591360
  eFloor := 325046403332259012692441628208773515828773158566380469260990178020224154347902863897964782654125514781480282801500587366208483832690337092993024
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1388707,width:=277741,den:=32768,localDen:=2361183241434822606848,lowerC:=2362989308773729828864,s:=[15483675500324864,-8869885464219648,2351362147024896],L:=[2363777633664510156759,-1029755592358494208,304298122610212864,-74430176921911296,11562756335468544],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor264Source.source.poly i) 1388707 277741 32768
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor264Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 40) (CoreQuotient.fused G u 0 40) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 40 WideAnchor264Source.data
    WideAnchor264Source.path_checked WideAnchor264Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor264Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 40 0) (CoreQuotient.fused G u 40 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 40 0 WideAnchor264Source.data
    WideAnchor264Source.path_swapped WideAnchor264Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor264Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor264Cell127
