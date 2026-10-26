/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor520Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor520Cell099
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (269581/1048576)
  b := (323497/1048576)
  s := [(4864810610369/17592186044416),(-98036784667/8796093022208),(-5342662383/2199023255552)]
  L := [(13108869723193136511/18446744073709551616),(176608257343/4398046511104),(26301959153/6597069766656),(-332962651/274877906944),(55346431/412316860416)]
  c := (1562699046515/2199023255552)
  R := (-17079940137229/100000000000000)
  total := (-2008153588437/250000000000000)
  k := 1
  n := 32
  sFloor := (289124733873/2199023255552)
  nFloor := (1212869739075/137438953472)
  eFloor := (967287969017/137438953472)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=269581,width:=53916,den:=1048576,localDen:=55340232221128654848,lowerC:=39326609169564303360,s:=[15303370951734853632,-616794117113905152,-134452501221998592],L:=[39326609169579409533,2222246160620322816,220636824966529024,-67034235789115392,7428472221728768],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor520Source.source.poly i) 269581 53916 1048576
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor520Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 5) (CoreQuotient.fused G u 4 5) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 4 5 WideAnchor520Source.data
    WideAnchor520Source.path_checked WideAnchor520Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor520Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 5 4) (CoreQuotient.fused G u 5 4) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 5 4 WideAnchor520Source.data
    WideAnchor520Source.path_swapped WideAnchor520Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor520Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor520Cell099
