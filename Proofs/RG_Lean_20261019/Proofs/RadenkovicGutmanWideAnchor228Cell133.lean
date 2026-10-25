/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor228Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor228Cell133
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (518331/4096)
  b := 128
  s := [(4550512483329/18446744073709551616),(-156837661753/18446744073709551616),(1751807947/9223372036854775808)]
  L := [(309523502199791430224591409/309485009821345068724781056),(-18818827/6597069766656),(161779/3298534883328),(-37/51539607552),(-1/206158430208)]
  c := (1099645296835/1099511627776)
  R := (6078195587/100000000000000)
  total := (279411371/3125000000000)
  k := 0
  n := 32
  sFloor := (2198589218735/18446744073709551616)
  nFloor := 37480750973457151769326367943294484406832256536744452930324140130304
  eFloor := 37476071373467641072271673662475831941750086909048951538537287647232
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=518331,width:=5957,den:=4096,localDen:=928455029464035206174343168,lowerC:=928567902949842087082721280,s:=[229034792530521096192,-7893897984495058944,176342761904013312],L:=[928570506599374290673774227,-2648514445773432160256,45536740257273217024,-666532744850833408,-4503599627370496],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor228Source.source.poly i) 518331 5957 4096
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor228Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 12) (CoreQuotient.fused G u 0 12) (((17/9) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (17/9) 0 12 WideAnchor228Source.data
    WideAnchor228Source.path_checked WideAnchor228Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor228Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 12 0) (CoreQuotient.fused G u 12 0) (((17/9) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (17/9) 12 0 WideAnchor228Source.data
    WideAnchor228Source.path_swapped WideAnchor228Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor228Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor228Cell133
