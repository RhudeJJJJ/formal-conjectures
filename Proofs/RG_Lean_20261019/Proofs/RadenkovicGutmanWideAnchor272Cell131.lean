/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor272Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor272Cell131
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1439809/16384)
  b := (863885/8192)
  s := [(3396267021293/4611686018427387904),(-486774782885/1152921504606846976),(64563305711/576460752303423488)]
  L := [(18894328324718035936649/18889465931478580854784),(-225638803/2199023255552),(33492085/1099511627776),(-257115/34359738368),(80133/68719476736)]
  c := (274927095861/274877906944)
  R := (8946611413/100000000000000)
  total := (1885889986417/1000000000000000)
  k := 0
  n := 32
  sFloor := (1965674335441/9223372036854775808)
  nFloor := 29574100089861528216930134458630398477012536027374742764785764394823414902279156694296431924260912290562017868460063175276246882704923219349486633454227910528505253575295322065044111647990070910434410496
  eFloor := 29566445714318970167563025092020496662089997308743251061421046210606884316519942772854205649908896163664201901249292289909213640069078968691527136327428067810369207361296861567616662582397319217959403520
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1439809,width:=287961,den:=16384,localDen:=18889465931478580854784,lowerC:=18892846168116031389696,s:=[13911109719216128,-7975318042787840,2115610401538048],L:=[18894328324718035936649,-1938222559187173376,575389638999408640,-141350466087813120,22026791317143552],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor272Source.source.poly i) 1439809 287961 16384
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor272Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 48) (CoreQuotient.fused G u 0 48) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 48 WideAnchor272Source.data
    WideAnchor272Source.path_checked WideAnchor272Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor272Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 48 0) (CoreQuotient.fused G u 48 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 48 0 WideAnchor272Source.data
    WideAnchor272Source.path_swapped WideAnchor272Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor272Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor272Cell131
