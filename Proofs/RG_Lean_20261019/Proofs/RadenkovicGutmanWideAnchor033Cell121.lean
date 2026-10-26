/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor033Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor033Cell121
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (116269/8192)
  b := (558091/32768)
  s := [(3087981571439/18014398509481984),(-3499333208995/36028797018963968),(459590044509/18014398509481984)]
  L := [(297923819165843652781/295147905179352825856),(-47814531205/13194139533312),(2272778977/2199023255552),(-200929793/824633720832),(5055219/137438953472)]
  c := (1106777093801/1099511627776)
  R := (82327079601/25000000000000)
  total := (2229124082963/200000000000000)
  k := 0
  n := 32
  sFloor := (898952505725/18014398509481984)
  nFloor := 2089394163434373897828029256517762836807333275649072156377088
  eFloor := 2069216588652402268362962302909170633888864256302312614526976
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=465076,width:=93015,den:=32768,localDen:=885443715538058477568,lowerC:=891294641594478624768,s:=[151780470199369728,-85999612944261120,22589769867706368],L:=[893771457497530958343,-3208778871860101120,915141691617312768,-215746722431762432,32568000418676736],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor033Source.source.poly i) 465076 93015 32768
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor033Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 10 12) (CoreQuotient.fused G u 10 12) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 10 12 WideAnchor033Source.data
    WideAnchor033Source.path_checked WideAnchor033Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor033Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 12 10) (CoreQuotient.fused G u 12 10) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 12 10 WideAnchor033Source.data
    WideAnchor033Source.path_swapped WideAnchor033Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor033Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor033Cell121
