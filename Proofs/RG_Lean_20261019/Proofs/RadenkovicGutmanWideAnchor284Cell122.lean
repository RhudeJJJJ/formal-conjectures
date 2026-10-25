/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor284Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor284Cell122
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (558091/32768)
  b := (669709/32768)
  s := [(7210613186209/72057594037927936),(-4106935856487/72057594037927936),(541752774445/36028797018963968)]
  L := [(37137710518064133119/36893488147419103232),(-34017955477/13194139533312),(4916489027/6597069766656),(-146984411/824633720832),(11223085/412316860416)]
  c := (1104608555827/1099511627776)
  R := (23124588097/10000000000000)
  total := (9408880336687/1000000000000000)
  k := 0
  n := 32
  sFloor := (1046795719653/36028797018963968)
  nFloor := 770523554406472262470688833536
  eFloor := 765303294665131750980818305024
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=558091,width:=111618,den:=32768,localDen:=110680464442257309696,lowerC:=111193538019345825792,s:=[11075501854017024,-6308253475564032,1664264523095040],L:=[111413131554192399357,-285363293458006016,82484998367608832,-19727913695838208,3012673939701760],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor284Source.source.poly i) 558091 111618 32768
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor284Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 8) (CoreQuotient.fused G u 0 8) (((13/7) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (13/7) 0 8 WideAnchor284Source.data
    WideAnchor284Source.path_checked WideAnchor284Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor284Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 8 0) (CoreQuotient.fused G u 8 0) (((13/7) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (13/7) 8 0 WideAnchor284Source.data
    WideAnchor284Source.path_swapped WideAnchor284Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor284Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor284Cell122
