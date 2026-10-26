/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor542Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor542Cell128
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (104153/2048)
  b := (249967/4096)
  s := [(8751651540971/2305843009213693952),(-2506907079011/1152921504606846976),(332306276713/576460752303423488)]
  L := [(1181494307019527610927/1180591620717411303424),(-668088709/2199023255552),(296459443/3298534883328),(-3024333/137438953472),(705209/206158430208)]
  c := (1100096661817/1099511627776)
  R := (26597192671/100000000000000)
  total := (3242739776327/1000000000000000)
  k := 0
  n := 32
  sFloor := (633382811225/576460752303423488)
  nFloor := 1899256389536947264396410086965485854273055239705073955789689936529562231504767184329747200219283456
  eFloor := 1897790906433753931374981016764404101521800460259712519846823431019598169230750430713823252392706048
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=208306,width:=41661,den:=4096,localDen:=3541774862152233910272,lowerC:=3543659388707090202624,s:=[13442536766931456,-7701218546721792,2041689764124672],L:=[3544482921058582832781,-1076032183493197824,318320903068844032,-77936467963281408,12115398367379456],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor542Source.source.poly i) 208306 41661 4096
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor542Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 5 20) (CoreQuotient.fused G u 5 20) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 5 20 WideAnchor542Source.data
    WideAnchor542Source.path_checked WideAnchor542Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor542Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 20 5) (CoreQuotient.fused G u 20 5) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 20 5 WideAnchor542Source.data
    WideAnchor542Source.path_swapped WideAnchor542Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor542Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor542Cell128
