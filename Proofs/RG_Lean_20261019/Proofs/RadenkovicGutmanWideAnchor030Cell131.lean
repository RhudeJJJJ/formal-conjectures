/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor030Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor030Cell131
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1439809/16384)
  b := (863885/8192)
  s := [(3395827472775/4611686018427387904),(-1946695666659/4611686018427387904),(129091458685/1152921504606846976)]
  L := [(2361790961915745925757/2361183241434822606848),(-1353482083/13194139533312),(200866453/6597069766656),(-6166979/824633720832),(480431/412316860416)]
  c := (274927091439/274877906944)
  R := (8945807199/100000000000000)
  total := (29463817519/15625000000000)
  k := 0
  n := 32
  sFloor := (245687205107/1152921504606846976)
  nFloor := 29574099099063388779085130610437842823489114480053861389877792595527989745668595577893265418754205914085667871218498493891842663836064429192665930036812076901017848959352384852604386511633399645755932672
  eFloor := 29566445714318970167563025092020496662089997308743251061421046210606884316519942772854205649908896163664201901249292289909213640069078968691527136327428067810369207361296861567616662582397319217959403520
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1439809,width:=287961,den:=16384,localDen:=7083549724304467820544,lowerC:=7084817199089439473664,s:=[5215990998182400,-2990124543988224,793137922160640],L:=[7085372885747237777271,-726645160275869696,215678711624630272,-52973946240237568,8253741731938304],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor030Source.source.poly i) 1439809 287961 16384
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor030Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 39) (CoreQuotient.fused G u 9 39) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 39 WideAnchor030Source.data
    WideAnchor030Source.path_checked WideAnchor030Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor030Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 39 9) (CoreQuotient.fused G u 39 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 39 9 WideAnchor030Source.data
    WideAnchor030Source.path_swapped WideAnchor030Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor030Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor030Cell131
