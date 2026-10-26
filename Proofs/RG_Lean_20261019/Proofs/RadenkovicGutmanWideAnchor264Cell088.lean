/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor264Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor264Cell088
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (72565/2097152)
  b := (43539/1048576)
  s := [(6223036155413/8796093022208),(-255380415715/8796093022208),(18552064481/4398046511104)]
  L := [(202720379242158222935/1180591620717411303424),(435895668659/17592186044416),(-4484534081/1649267441664),(113796327/274877906944),(-27224129/824633720832)]
  c := (755192262091/4398046511104)
  R := (-88097168898219/100000000000000)
  total := (-293648979427/50000000000000)
  k := 3
  n := 32
  sFloor := (1501189967165/4398046511104)
  nFloor := (1296146404135/8796093022208)
  eFloor := (1293185918775/8796093022208)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=72565,width:=14513,den:=2097152,localDen:=3541774862152233910272,lowerC:=608161137726207295488,s:=[2505725322124163284992,-102829737518888386560,14940095666095915008],L:=[608161137726474668805,87757389438677680128,-9630463607846207488,1466254508609765376,-116926743717085184],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor264Source.source.poly i) 72565 14513 2097152
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor264Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 40) (CoreQuotient.fused G u 0 40) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 40 WideAnchor264Source.data
    WideAnchor264Source.path_checked WideAnchor264Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor264Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 40 0) (CoreQuotient.fused G u 40 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 40 0 WideAnchor264Source.data
    WideAnchor264Source.path_swapped WideAnchor264Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor264Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor264Cell088
