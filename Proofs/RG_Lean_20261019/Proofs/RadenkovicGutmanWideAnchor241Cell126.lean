/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor241Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor241Cell126
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (144657/4096)
  b := (1388707/32768)
  s := [(1631815336743/144115188075855872),(-1868740403471/288230376151711744),(247603418479/144115188075855872)]
  L := [(295613474408433472407/295147905179352825856),(-1374215803/2199023255552),(202621275/1099511627776),(-6182537/137438953472),(479521/68719476736)]
  c := (1100719733721/1099511627776)
  R := (13727034433/25000000000000)
  total := (929287194293/200000000000000)
  k := 0
  n := 32
  sFloor := (1890097106973/576460752303423488)
  nFloor := 814121295489548029273287865546752738967006463122254851955764893022076275549706125312
  eFloor := 812820702723232157420679599911376717149956351646693884169236612149895968157406855168
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1157256,width:=231451,den:=32768,localDen:=295147905179352825856,lowerC:=295472203649595211776,s:=[3341957809649664,-1913590173154304,507091801044992],L:=[295613474408433472407,-184444122860355584,54390734349926400,-13276897110654976,2059527012745216],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor241Source.source.poly i) 1157256 231451 32768
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor241Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 23) (CoreQuotient.fused G u 0 23) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 23 WideAnchor241Source.data
    WideAnchor241Source.path_checked WideAnchor241Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor241Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 23 0) (CoreQuotient.fused G u 23 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 23 0 WideAnchor241Source.data
    WideAnchor241Source.path_swapped WideAnchor241Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor241Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor241Cell126
