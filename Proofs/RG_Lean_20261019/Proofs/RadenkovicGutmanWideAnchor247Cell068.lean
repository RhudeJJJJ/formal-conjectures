/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor247Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor247Cell068
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (969115/1073741824)
  b := (581469/536870912)
  s := [(2199005623581/2199023255552),(-7052721/2199023255552),(-352617/1099511627776)]
  L := [(702293927034206412659067775/81129638414606681695789005144064),(2994038767951/864691128455135232),(149697874229/432345564227567616),(-101617/54043195528445952),(-2537/27021597764222976)]
  c := (311881155139/36028797018963968)
  R := (-291430172290573/50000000000000)
  total := (-1035211642991/1000000000000000)
  k := 17
  n := 32
  sFloor := (1099498932813/2199023255552)
  nFloor := (1463788064645/72057594037927936)
  eFloor := (1355849881355/144115188075855872)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=969115,width:=193823,den:=1073741824,localDen:=243388915243820045087367015432192,lowerC:=2106881781101820380411068416,s:=[243386963729080732675307917541376,-780598435861661415496482816,-78055626660470891546148864],L:=[2106881781102619237977203325,842746992479808908852985856,84272411324484972024168448,-457642283334507692032,-22851264509277896704],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor247Source.source.poly i) 969115 193823 1073741824
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor247Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 2) (CoreQuotient.fused G u 0 2) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 2 WideAnchor247Source.data
    WideAnchor247Source.path_checked WideAnchor247Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor247Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 0) (CoreQuotient.fused G u 2 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 2 0 WideAnchor247Source.data
    WideAnchor247Source.path_swapped WideAnchor247Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor247Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor247Cell068
