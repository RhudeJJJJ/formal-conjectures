/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor027Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor027Cell108
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (10867/8192)
  b := (1669171/1048576)
  s := [(4604232365611/70368744177664),(-716608842095/35184372088832),(14017448245/4398046511104)]
  L := [(350236536155895589373/295147905179352825856),(220294906201/13194139533312),(-79147970611/6597069766656),(1973500271/824633720832),(-100061885/412316860416)]
  c := (326183192577/274877906944)
  R := (4278303490651/50000000000000)
  total := (5811906523513/250000000000000)
  k := 0
  n := 32
  sFloor := (848823463335/35184372088832)
  nFloor := 455272542335609491452592128
  eFloor := 336539883256136553396699136
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1390976,width:=278195,den:=1048576,localDen:=885443715538058477568,lowerC:=1050709608467313721344,s:=[57934650684035039232,-18034051997006561280,2822085083702231040],L:=[1050709608467686768119,14783740900135665664,-10623060791219191808,2119029780648034304,-214881261825556480],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor027Source.source.poly i) 1390976 278195 1048576
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor027Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 36) (CoreQuotient.fused G u 9 36) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 36 WideAnchor027Source.data
    WideAnchor027Source.path_checked WideAnchor027Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor027Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 36 9) (CoreQuotient.fused G u 36 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 36 9 WideAnchor027Source.data
    WideAnchor027Source.path_swapped WideAnchor027Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor027Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor027Cell108
