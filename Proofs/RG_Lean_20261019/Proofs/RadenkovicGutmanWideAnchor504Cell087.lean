/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor504Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor504Cell087
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (483767/16777216)
  b := (72565/2097152)
  s := [(6949920541087/8796093022208),(-181293624429/4398046511104),(3771501649/1099511627776)]
  L := [(27473408819923902657/295147905179352825856),(4942859588965/211106232532992),(-59077691797/105553116266496),(-595487851/13194139533312),(102027961/6597069766656)]
  c := (204692846685/2199023255552)
  R := (-118712900965689/100000000000000)
  total := (-1628919692017/250000000000000)
  k := 4
  n := 32
  sFloor := (1654376326355/4398046511104)
  nFloor := (1197286829429/17592186044416)
  eFloor := (1508088928985/17592186044416)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=483767,width:=96753,den:=16777216,localDen:=885443715538058477568,lowerC:=82420226459739095040,s:=[699601908603920842752,-36499227557618515968,3037214294862200832],L:=[82420226459771707971,20731855745434255360,-495579598029848576,-39962513206411264,13693961117892608],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor504Source.source.poly i) 483767 96753 16777216
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor504Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 34) (CoreQuotient.fused G u 4 34) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 4 34 WideAnchor504Source.data
    WideAnchor504Source.path_checked WideAnchor504Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor504Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 34 4) (CoreQuotient.fused G u 34 4) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 34 4 WideAnchor504Source.data
    WideAnchor504Source.path_swapped WideAnchor504Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor504Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor504Cell087
