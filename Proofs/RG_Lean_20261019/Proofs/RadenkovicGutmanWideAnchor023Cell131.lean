/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor023Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor023Cell131
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1439809/16384)
  b := (863885/8192)
  s := [(3395827472775/4611686018427387904),(-1946695666659/4611686018427387904),(129091458685/1152921504606846976)]
  L := [(9447163847621258908281/9444732965739290427392),(-1353482083/13194139533312),(200866453/6597069766656),(-6166979/824633720832),(480431/412316860416)]
  c := (1099708365751/1099511627776)
  R := (2236451743/25000000000000)
  total := (94284214123/50000000000000)
  k := 0
  n := 32
  sFloor := (245687205107/1152921504606846976)
  nFloor := 18019161005789976861570020663631253387477802715125912631106247843186812283261752128596867669301040217706078034869669930781621468109165398574372319130993711821961648614146048000
  eFloor := 18014497885831321363997862012141210325638270581042254651078783678779223702825529286540571488470984221732585308023804638355760920280130416083620953675413474416047442058767499264
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1439809,width:=287961,den:=16384,localDen:=28334198897217871282176,lowerC:=28339268796228908875776,s:=[20863963992729600,-11960498175952896,3172551688642560],L:=[28341491542863776724843,-2906580641103478784,862714846498521088,-211895784960950272,33014966927753216],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor023Source.source.poly i) 1439809 287961 16384
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor023Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 32) (CoreQuotient.fused G u 9 32) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 32 WideAnchor023Source.data
    WideAnchor023Source.path_checked WideAnchor023Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor023Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 32 9) (CoreQuotient.fused G u 32 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 32 9 WideAnchor023Source.data
    WideAnchor023Source.path_swapped WideAnchor023Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor023Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor023Cell131
