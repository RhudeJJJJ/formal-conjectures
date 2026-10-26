/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor038Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor038Cell107
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1159147/1048576)
  b := (10867/8192)
  s := [(754060489785/8796093022208),(-1661803116875/70368744177664),(116785598975/35184372088832)]
  L := [(1372839078971394151339/1180591620717411303424),(155706653143/4398046511104),(-88719540317/6597069766656),(551014355/274877906944),(-62530303/412316860416)]
  c := (159819503195/137438953472)
  R := (3771630741039/50000000000000)
  total := (17969276647543/1000000000000000)
  k := 0
  n := 32
  sFloor := (575531499919/17592186044416)
  nFloor := 216119715031552
  eFloor := 156505612766720
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1159147,width:=231829,den:=1048576,localDen:=3541774862152233910272,lowerC:=4118517236912955064320,s:=[303624857140529725440,-83641289523855360000,11756023318157721600],L:=[4118517236914182454017,125391559316025114624,-47630940522208559104,7099765903054602240,-537131212787941376],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor038Source.source.poly i) 1159147 231829 1048576
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor038Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 10 17) (CoreQuotient.fused G u 10 17) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 10 17 WideAnchor038Source.data
    WideAnchor038Source.path_checked WideAnchor038Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor038Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 17 10) (CoreQuotient.fused G u 17 10) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 17 10 WideAnchor038Source.data
    WideAnchor038Source.path_swapped WideAnchor038Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor038Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor038Cell107
