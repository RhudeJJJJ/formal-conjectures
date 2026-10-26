/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor036Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor036Cell125
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (241095/8192)
  b := (144657/4096)
  s := [(2813490889795/144115188075855872),(-402208931383/36028797018963968),(212928021769/72057594037927936)]
  L := [(2366519978237572648617/2361183241434822606848),(-5885945809/6597069766656),(36006871/137438953472),(-3281671/51539607552),(338235/34359738368)]
  c := (275311154511/274877906944)
  R := (39372616333/50000000000000)
  total := (2774819430707/500000000000000)
  k := 0
  n := 32
  sFloor := (1630511207801/288230376151711744)
  nFloor := 33139004637031106483699126905466462390739840559257053525817066764154148920868831494144
  eFloor := 33062981650082987201365720276246070114867346465014368780255293413649757330643215187968
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=241095,width:=48219,den:=8192,localDen:=7083549724304467820544,lowerC:=7094714429092487233536,s:=[138288704215203840,-79077493581348864,20931676251979776],L:=[7099559934712717945851,-6319986188920815616,1855780000515489792,-451029427879411712,69729996641402880],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor036Source.source.poly i) 241095 48219 8192
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor036Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 10 15) (CoreQuotient.fused G u 10 15) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 10 15 WideAnchor036Source.data
    WideAnchor036Source.path_checked WideAnchor036Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor036Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 15 10) (CoreQuotient.fused G u 15 10) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 15 10 WideAnchor036Source.data
    WideAnchor036Source.path_swapped WideAnchor036Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor036Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor036Cell125
