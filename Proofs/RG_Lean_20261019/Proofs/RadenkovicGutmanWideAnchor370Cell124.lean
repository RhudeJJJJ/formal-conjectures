/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor370Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor370Cell124
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1607301/65536)
  b := (241095/8192)
  s := [(4850815081853/144115188075855872),(-5540196720827/288230376151711744),(732414032927/144115188075855872)]
  L := [(1184412155148013045041/1180591620717411303424),(-16786191889/13194139533312),(2452667735/6597069766656),(-74145359/824633720832),(5709793/412316860416)]
  c := (550998036003/549755813888)
  R := (112851991611/100000000000000)
  total := (6623138866043/1000000000000000)
  k := 0
  n := 32
  sFloor := (1406565377183/144115188075855872)
  nFloor := 619129826036133707707957284358620343741448192
  eFloor := 617091160733071907604249441475711967246155776
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1607301,width:=321459,den:=65536,localDen:=3541774862152233910272,lowerC:=3549777817189673336832,s:=[119213631451619328,-68077937305522176,17999807273213952],L:=[3553236465444039135123,-4506009074227216384,1316765963722424320,-318451892055179264,49046748403859456],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor370Source.source.poly i) 1607301 321459 65536
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor370Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 10) (CoreQuotient.fused G u 2 10) (((21/11) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (21/11) 2 10 WideAnchor370Source.data
    WideAnchor370Source.path_checked WideAnchor370Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor370Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 10 2) (CoreQuotient.fused G u 10 2) (((21/11) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (21/11) 10 2 WideAnchor370Source.data
    WideAnchor370Source.path_swapped WideAnchor370Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor370Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor370Cell124
