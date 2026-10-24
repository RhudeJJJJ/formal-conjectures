/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanSymbolicAnchor005Source
namespace Gebendorfer.RadenkovicGutman.SymbolicAnchor005Cell149
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1470563/268435456)
  b := (1617619/268435456)
  s := [(3309659135591/4398046511104),(-276894539685/8796093022208),(3066991555/4398046511104)]
  L := [(11153142499596391758315/75557863725914323419136),(753738252477/35184372088832),(-2209757009/52776558133248),(-96948551/2199023255552),(8773253/3298534883328)]
  c := (20287448023/137438953472)
  R := (-19131774729551/20000000000000)
  total := (-505106800973/1000000000000000)
  k := 3
  n := 32
  sFloor := (1587139428651/4398046511104)
  nFloor := (477024034999/281474976710656)
  eFloor := (456332137155/281474976710656)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1470563,width:=147056,den:=268435456,localDen:=226673591177742970257408,lowerC:=33459427498784584630272,s:=[170578532979251695583232,-7135517954328294850560,158071541109998223360],L:=[33459427498789175274945,4855921716199358988288,-9490834085761777664,-9993380542550114304,602893355432542208],transformed:=fun i => IntegerPolynomialPaymentCell.affine (SymbolicAnchor005Source.source.poly i) 1470563 147056 268435456
}
theorem checked : IntegerPolynomialPaymentCell.checks SymbolicAnchor005Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 14) (CoreQuotient.fused G u 9 14) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 14 SymbolicAnchor005Source.data
    SymbolicAnchor005Source.path_checked SymbolicAnchor005Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry SymbolicAnchor005Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 14 9) (CoreQuotient.fused G u 14 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 14 9 SymbolicAnchor005Source.data
    SymbolicAnchor005Source.path_swapped SymbolicAnchor005Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry SymbolicAnchor005Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.SymbolicAnchor005Cell149
