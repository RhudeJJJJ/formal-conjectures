/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor418Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor418Cell113
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (865297/262144)
  b := (259589/65536)
  s := [(5684415750627/562949953421312),(-5433427713725/1125899906842624),(617995708269/562949953421312)]
  L := [(328252870106617870775/295147905179352825856),(-365221566547/13194139533312),(24086810077/6597069766656),(-54108635/824633720832),(-25845649/412316860416)]
  c := (1196275503673/1099511627776)
  R := (4217343838667/100000000000000)
  total := (31307183984247/1000000000000000)
  k := 0
  n := 32
  sFloor := (224106100127/70368744177664)
  nFloor := (921932206261/4)
  eFloor := (1624759930089/8)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=865297,width:=173059,den:=262144,localDen:=885443715538058477568,lowerC:=963368280990274289664,s:=[8940812895194185728,-4273021423760179200,972023201690812416],L:=[984758610319853612325,-24509604439269572608,3232876923302445056,-58098704439050240,-55503108599447552],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor418Source.source.poly i) 865297 173059 262144
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor418Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 4) (CoreQuotient.fused G u 2 4) (((40/21) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (40/21) 2 4 WideAnchor418Source.data
    WideAnchor418Source.path_checked WideAnchor418Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor418Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 2) (CoreQuotient.fused G u 4 2) (((40/21) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (40/21) 4 2 WideAnchor418Source.data
    WideAnchor418Source.path_swapped WideAnchor418Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor418Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor418Cell113
