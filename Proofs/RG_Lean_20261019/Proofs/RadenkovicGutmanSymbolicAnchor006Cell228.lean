/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanSymbolicAnchor006Source
namespace Gebendorfer.RadenkovicGutman.SymbolicAnchor006Cell228
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1337095/131072)
  b := (367701/32768)
  s := [(4082724631163/9007199254740992),(-1179053776647/9007199254740992),(91929865057/4503599627370496)]
  L := [(4805681736207448450715/4722366482869645213696),(-10930386305/3298534883328),(1515804923/3298534883328),(-22538429/412316860416),(997135/206158430208)]
  c := (557858496809/549755813888)
  R := (365778384561/50000000000000)
  total := (1631917587673/200000000000000)
  k := 0
  n := 32
  sFloor := (1543765292315/9007199254740992)
  nFloor := 1036608173522762078315343966045621348782994256565966471168
  eFloor := 1017713655675161884231190332570771359226459001005633699840
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1337095,width:=133709,den:=131072,localDen:=14167099448608935641088,lowerC:=14375903997542252150784,s:=[6421570594269560832,-1854491239352107008,289186350546026496],L:=[14417045208622345352145,-46945651712621281280,6510332571400798208,-774414523665743872,68522595435151360],transformed:=fun i => IntegerPolynomialPaymentCell.affine (SymbolicAnchor006Source.source.poly i) 1337095 133709 131072
}
theorem checked : IntegerPolynomialPaymentCell.checks SymbolicAnchor006Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 15) (CoreQuotient.fused G u 9 15) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 15 SymbolicAnchor006Source.data
    SymbolicAnchor006Source.path_checked SymbolicAnchor006Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry SymbolicAnchor006Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 15 9) (CoreQuotient.fused G u 15 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 15 9 SymbolicAnchor006Source.data
    SymbolicAnchor006Source.path_swapped SymbolicAnchor006Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry SymbolicAnchor006Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.SymbolicAnchor006Cell228
