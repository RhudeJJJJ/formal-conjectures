/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor545Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor545Cell131
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1439809/16384)
  b := (863885/8192)
  s := [(3395827472775/4611686018427387904),(-7786782666637/18446744073709551616),(1032731669481/9223372036854775808)]
  L := [(9447163847495967559679/9444732965739290427392),(-1353482083/13194139533312),(200866453/6597069766656),(-6166979/824633720832),(480431/412316860416)]
  c := (1099708365737/1099511627776)
  R := (8736139/97656250000)
  total := (1885684166001/1000000000000000)
  k := 0
  n := 32
  sFloor := (245687205107/1152921504606846976)
  nFloor := 51672928154388743233351221189737696758620308359884370693213218759067392181957537194464362097488284982085783043910934489726976
  eFloor := 51659555885711138466091733167148856228772779778939731965703032322206206349815820564793707236608202695316289363578267654684672
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1439809,width:=287961,den:=16384,localDen:=28334198897217871282176,lowerC:=28339268795868131622912,s:=[20863963992729600,-11960498175954432,3172551688645632],L:=[28341491542487902679037,-2906580641103478784,862714846498521088,-211895784960950272,33014966927753216],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor545Source.source.poly i) 1439809 287961 16384
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor545Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 5 23) (CoreQuotient.fused G u 5 23) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 5 23 WideAnchor545Source.data
    WideAnchor545Source.path_checked WideAnchor545Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor545Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 23 5) (CoreQuotient.fused G u 23 5) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 23 5 WideAnchor545Source.data
    WideAnchor545Source.path_swapped WideAnchor545Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor545Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor545Cell131
