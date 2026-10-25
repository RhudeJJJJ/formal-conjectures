/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor245Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor245Cell130
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1199841/16384)
  b := (1439809/16384)
  s := [(2933859180617/2305843009213693952),(-6727295677751/9223372036854775808),(892196498935/4611686018427387904)]
  L := [(9448229348827769144343/9444732965739290427392),(-1945573487/13194139533312),(288564679/6597069766656),(-8854813/824633720832),(689585/412316860416)]
  c := (1099794655803/1099511627776)
  R := (804310519/6250000000000)
  total := (1130150449681/500000000000000)
  k := 0
  n := 32
  sFloor := (849066755323/2305843009213693952)
  nFloor := 82733178357595594464833825293335291177614922577342590922941826214458565493642735051112080278724626988578153280045056
  eFloor := 82702351792528282683881859505069560513590124635699233560432049437967463521001809670178509540282291218304031206146048
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1199841,width:=239968,den:=16384,localDen:=28334198897217871282176,lowerC:=28341492473936769712128,s:=[36051261611421696,-20666252322051072,5481655289456640],L:=[28344688046483307433029,-4178087249314840576,1239375859085737984,-304249057977565184,47387920364994560],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor245Source.source.poly i) 1199841 239968 16384
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor245Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 27) (CoreQuotient.fused G u 0 27) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 27 WideAnchor245Source.data
    WideAnchor245Source.path_checked WideAnchor245Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor245Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 27 0) (CoreQuotient.fused G u 27 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 27 0 WideAnchor245Source.data
    WideAnchor245Source.path_swapped WideAnchor245Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor245Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor245Cell130
