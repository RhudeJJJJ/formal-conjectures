/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor433Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor433Cell122
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (558091/32768)
  b := (669709/32768)
  s := [(898262249749/9007199254740992),(-4084615488939/72057594037927936),(537886285113/36028797018963968)]
  L := [(148547510076686738705/147573952589676412928),(-33784217231/13194139533312),(4860180733/6597069766656),(-144553381/824633720832),(10990235/412316860416)]
  c := (276149111109/274877906944)
  R := (28837207127/12500000000000)
  total := (2345470338287/250000000000000)
  k := 0
  n := 32
  sFloor := (2088627539639/72057594037927936)
  nFloor := 65737634387573470959318716297248768
  eFloor := 65293774131961564771566919245365248
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=558091,width:=111618,den:=32768,localDen:=442721857769029238784,lowerC:=444769275387234484224,s:=[44151386099662848,-25095877564041216,6609546671468544],L:=[445642530230060216115,-1133610219750817792,326161207826317312,-77606505490153472,11800674975088640],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor433Source.source.poly i) 558091 111618 32768
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor433Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 8) (CoreQuotient.fused G u 2 8) (((13/7) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (13/7) 2 8 WideAnchor433Source.data
    WideAnchor433Source.path_checked WideAnchor433Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor433Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 8 2) (CoreQuotient.fused G u 8 2) (((13/7) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (13/7) 8 2 WideAnchor433Source.data
    WideAnchor433Source.path_swapped WideAnchor433Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor433Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor433Cell122
