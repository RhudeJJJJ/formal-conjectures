/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor531Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor531Cell128
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (104153/2048)
  b := (249967/4096)
  s := [(4375825770485/1152921504606846976),(-5013814158019/2305843009213693952),(664612553425/1152921504606846976)]
  L := [(590747153454497216265/590295810358705651712),(-668088709/2199023255552),(296459443/3298534883328),(-3024333/137438953472),(705209/206158430208)]
  c := (550048330857/549755813888)
  R := (26597187989/100000000000000)
  total := (202671206277/62500000000000)
  k := 0
  n := 32
  sFloor := (633382811225/576460752303423488)
  nFloor := 54371146800689469216056984026059300276555414426910040237539328
  eFloor := 54329193540802207350759087286683520480290065139039715404546048
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=208306,width:=41661,den:=4096,localDen:=1770887431076116955136,lowerC:=1771829694187651989504,s:=[6721268383464960,-3850609273358592,1020844882060800],L:=[1772241460363491648795,-538016091746598912,159160451534422016,-38968233981640704,6057699183689728],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor531Source.source.poly i) 208306 41661 4096
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor531Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 5 9) (CoreQuotient.fused G u 5 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 5 9 WideAnchor531Source.data
    WideAnchor531Source.path_checked WideAnchor531Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor531Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 5) (CoreQuotient.fused G u 9 5) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 5 WideAnchor531Source.data
    WideAnchor531Source.path_swapped WideAnchor531Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor531Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor531Cell128
