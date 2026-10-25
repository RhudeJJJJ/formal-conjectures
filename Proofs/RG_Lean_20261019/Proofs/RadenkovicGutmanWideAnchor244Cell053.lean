/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor244Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor244Cell053
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1006419/17179869184)
  b := (603851/8589934592)
  s := [(1099510834567/1099511627776),(-634563/2199023255552),(-1983/68719476736)]
  L := [(836504763919/2305843009213693952),(501900242579/3458764513820540928),(50189576405/3458764513820540928),(-6211/432345564227567616),(-155/216172782113783808)]
  c := (836504763919/2305843009213693952)
  R := (-370736999043451/50000000000000)
  total := (-85774486247/1000000000000000)
  k := 22
  n := 32
  sFloor := (2199020971115/4398046511104)
  nFloor := (922713586805/4611686018427387904)
  eFloor := (57341113323/288230376151711744)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1006419,width:=201283,den:=17179869184,localDen:=6917529027641081856,lowerC:=2509514291757,s:=[6917524037201559552,-1996162596864,-199615315968],L:=[2509514291757,1003800485158,100379152810,-99376,-4960],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor244Source.source.poly i) 1006419 201283 17179869184
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor244Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 26) (CoreQuotient.fused G u 0 26) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 26 WideAnchor244Source.data
    WideAnchor244Source.path_checked WideAnchor244Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor244Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 26 0) (CoreQuotient.fused G u 26 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 26 0 WideAnchor244Source.data
    WideAnchor244Source.path_swapped WideAnchor244Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor244Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor244Cell053
