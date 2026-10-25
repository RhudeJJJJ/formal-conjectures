/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor018Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor018Cell128
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (104153/2048)
  b := (249967/4096)
  s := [(4375825770485/1152921504606846976),(-5013814158023/2305843009213693952),(664612553427/1152921504606846976)]
  L := [(4725977228258699061299/4722366482869645213696),(-668088709/2199023255552),(296459443/3298534883328),(-3024333/137438953472),(705209/206158430208)]
  c := (1100096661859/1099511627776)
  R := (1329859729/5000000000000)
  total := (3242739970689/1000000000000000)
  k := 0
  n := 32
  sFloor := (633382811225/576460752303423488)
  nFloor := 66343548838839767222521228232514954170114051223354937180906458867082903883501037407691741832880656896991404121253213339913480248991154176
  eFloor := 66292357567206604813972862953631212001342530841454055650323489726373487395614779072140879297837748738669503421858694240924691532382994432
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=208306,width:=41661,den:=4096,localDen:=14167099448608935641088,lowerC:=14174637555369526689792,s:=[53770147067719680,-30804874186893312,8166759056510976],L:=[14177931684776097183897,-4304128733972791296,1273283612275376128,-311745871853125632,48461593469517824],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor018Source.source.poly i) 208306 41661 4096
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor018Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 27) (CoreQuotient.fused G u 9 27) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 27 WideAnchor018Source.data
    WideAnchor018Source.path_checked WideAnchor018Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor018Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 27 9) (CoreQuotient.fused G u 27 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 27 9 WideAnchor018Source.data
    WideAnchor018Source.path_swapped WideAnchor018Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor018Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor018Cell128
