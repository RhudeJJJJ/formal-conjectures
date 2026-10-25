/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor507Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor507Cell084
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (139979/8388608)
  b := (671899/33554432)
  s := [(3596137142587/4398046511104),(-184302613667/4398046511104),(3405226389/1099511627776)]
  L := [(31244702596519046087/295147905179352825856),(1410792179239/52776558133248),(-16415449087/13194139533312),(-645085627/3298534883328),(31266685/824633720832)]
  c := (931164699689/8796093022208)
  R := (-11228133796411/10000000000000)
  total := (-355843565771/100000000000000)
  k := 4
  n := 32
  sFloor := (856363858619/2199023255552)
  nFloor := (1011209749121/35184372088832)
  eFloor := (479099446111/17592186044416)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=559916,width:=111983,den:=33554432,localDen:=885443715538058477568,lowerC:=93734107789544914944,s:=[723998035281658773504,-37105017106269732864,2742250495543345152],L:=[93734107789557138261,23669165122203418624,-1101622140278407168,-173163854442790912,33572347382333440],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor507Source.source.poly i) 559916 111983 33554432
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor507Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 37) (CoreQuotient.fused G u 4 37) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 4 37 WideAnchor507Source.data
    WideAnchor507Source.path_checked WideAnchor507Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor507Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 37 4) (CoreQuotient.fused G u 37 4) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 37 4 WideAnchor507Source.data
    WideAnchor507Source.path_swapped WideAnchor507Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor507Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor507Cell084
