/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor537Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor537Cell039
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (627095/137438953472)
  b := (376257/68719476736)
  s := [(1099509470591/1099511627776),(-1725743/2199023255552),(-43143/549755813888)]
  L := [(5852407567485/4611686018427387904),(7022875102603/13835058055282163712),(351140959517/6917529027641081856),(-69901/864691128455135232),(-1745/432345564227567616)]
  c := (1463101891871/1152921504606846976)
  R := (-339431273805263/50000000000000)
  total := (-3054690073/500000000000000)
  k := 20
  n := 32
  sFloor := (2199017042867/4398046511104)
  nFloor := (368124482789/295147905179352825856)
  eFloor := (1138250491791/1180591620717411303424)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=627095,width:=125419,den:=137438953472,localDen:=13835058055282163712,lowerC:=17557222702452,s:=[13835030911613140992,-10857436151808,-1085729144832],L:=[17557222702455,7022875102603,702281919034,-1118416,-55840],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor537Source.source.poly i) 627095 125419 137438953472
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor537Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 5 15) (CoreQuotient.fused G u 5 15) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 5 15 WideAnchor537Source.data
    WideAnchor537Source.path_checked WideAnchor537Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor537Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 15 5) (CoreQuotient.fused G u 15 5) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 15 5 WideAnchor537Source.data
    WideAnchor537Source.path_swapped WideAnchor537Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor537Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor537Cell039
