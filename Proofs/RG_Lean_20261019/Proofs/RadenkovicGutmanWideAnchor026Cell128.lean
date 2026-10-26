/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor026Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor026Cell128
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (104153/2048)
  b := (249967/4096)
  s := [(4375825770485/1152921504606846976),(-5013814158019/2305843009213693952),(664612553425/1152921504606846976)]
  L := [(2362988614173752877769/2361183241434822606848),(-668088709/2199023255552),(296459443/3298534883328),(-3024333/137438953472),(705209/206158430208)]
  c := (137512082735/137438953472)
  R := (13298597767/50000000000000)
  total := (1621370033109/500000000000000)
  k := 0
  n := 32
  sFloor := (633382811225/576460752303423488)
  nFloor := 133645745364009063608705505719580863655175545958759612929499307617325641530335118110311679106640848962222466021379612473389894687100935216657101073727526016701693952
  eFloor := 133542623119577394691529364349263047632062881688462449057038021769641792255215395256907643771835619713340458107505568507347911463881853109067213205100321638042304512
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=208306,width:=41661,den:=4096,localDen:=7083549724304467820544,lowerC:=7087318777820054814720,s:=[26885073533859840,-15402437093434368,4083379528243200],L:=[7088965842521258633307,-2152064366986395648,636641806137688064,-155872935926562816,24230796734758912],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor026Source.source.poly i) 208306 41661 4096
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor026Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 35) (CoreQuotient.fused G u 9 35) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 35 WideAnchor026Source.data
    WideAnchor026Source.path_checked WideAnchor026Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor026Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 35 9) (CoreQuotient.fused G u 35 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 35 9 WideAnchor026Source.data
    WideAnchor026Source.path_swapped WideAnchor026Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor026Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor026Cell128
