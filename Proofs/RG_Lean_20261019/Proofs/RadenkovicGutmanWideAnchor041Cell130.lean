/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor041Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor041Cell130
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1199841/16384)
  b := (1439809/16384)
  s := [(5866625065585/4611686018427387904),(-1681322214371/2305843009213693952),(222961708983/1152921504606846976)]
  L := [(9448228697276596509907/9444732965739290427392),(-972423799/6597069766656),(48064455/1099511627776),(-4423505/412316860416),(114805/68719476736)]
  c := (137474327397/137438953472)
  R := (1286730313/10000000000000)
  total := (2259946056779/1000000000000000)
  k := 0
  n := 32
  sFloor := (1697913736387/4611686018427387904)
  nFloor := 12775806761550826871458146205659438431235508201060677307230300261614792382340780093950369411747849388782019060169162920082538496
  eFloor := 12771047354568996303651110913160003745883107476570973561600675605997217712042947888041853072729526643779663783942911701286912000
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1199841,width:=239968,den:=16384,localDen:=28334198897217871282176,lowerC:=28341491530066166808576,s:=[36044544402954240,-20660087370190848,5479506959966208],L:=[28344686091829789529721,-4176528414557077504,1238611573950382080,-303980948939079680,47336037160058880],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor041Source.source.poly i) 1199841 239968 16384
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
end Gebendorfer.RadenkovicGutman.WideAnchor041Cell130
