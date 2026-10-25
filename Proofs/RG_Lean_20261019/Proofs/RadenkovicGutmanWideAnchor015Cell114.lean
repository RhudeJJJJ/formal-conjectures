/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor015Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor015Cell114
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (259589/65536)
  b := (1246027/262144)
  s := [(7209591713663/1125899906842624),(-452629316459/140737488355328),(26841222125/35184372088832)]
  L := [(1285930764540587062023/1180591620717411303424),(-339715113685/13194139533312),(10429350269/2199023255552),(-470421917/824633720832),(4087175/137438953472)]
  c := (1173926900913/1099511627776)
  R := (818604350221/25000000000000)
  total := (1483434830943/50000000000000)
  k := 0
  n := 32
  sFloor := (1111869072497/562949953421312)
  nFloor := 25570995107067089609685531495543914351724331008
  eFloor := 23177560883774709844489875277172006943176261632
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1038356,width:=207671,den:=262144,localDen:=3541774862152233910272,lowerC:=3781483235486975655936,s:=[22679414522237681664,-11390789715247497216,2701925887770624000],L:=[3857792293621761186069,-91191581452124815360,16797644371456425984,-2020446748836626432,105325697748172800],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor015Source.source.poly i) 1038356 207671 262144
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor015Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 24) (CoreQuotient.fused G u 9 24) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 24 WideAnchor015Source.data
    WideAnchor015Source.path_checked WideAnchor015Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor015Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 24 9) (CoreQuotient.fused G u 24 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 24 9 WideAnchor015Source.data
    WideAnchor015Source.path_swapped WideAnchor015Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor015Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor015Cell114
