/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor266Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor266Cell130
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1199841/16384)
  b := (1439809/16384)
  s := [(2933859180617/2305843009213693952),(-3363647838875/4611686018427387904),(446098249467/2305843009213693952)]
  L := [(1181028668629652140753/1180591620717411303424),(-1945573487/13194139533312),(288564679/6597069766656),(-8854813/824633720832),(689585/412316860416)]
  c := (274948663957/274877906944)
  R := (12868969441/100000000000000)
  total := (90412042471/40000000000000)
  k := 0
  n := 32
  sFloor := (849066755323/2305843009213693952)
  nFloor := 7264788693104285733262856325267212230637428796044208402365261414182033601530044416910443836471958852861655246966763246298262029056283072718933738810910884454729461203468288
  eFloor := 7262081816781048300694715156592232797732143837800071394293605303865726986429405794148000607614769458562719366529129867844944541634998159649085244397325761604797497937494016
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1199841,width:=239968,den:=16384,localDen:=3541774862152233910272,lowerC:=3542686559322626850816,s:=[4506407701427712,-2583281540256000,685206911181312],L:=[3543086005888956422259,-522260906164355072,154921982385717248,-38031132247195648,5923490045624320],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor266Source.source.poly i) 1199841 239968 16384
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor266Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 42) (CoreQuotient.fused G u 0 42) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 42 WideAnchor266Source.data
    WideAnchor266Source.path_checked WideAnchor266Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor266Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 42 0) (CoreQuotient.fused G u 42 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 42 0 WideAnchor266Source.data
    WideAnchor266Source.path_swapped WideAnchor266Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor266Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor266Cell130
