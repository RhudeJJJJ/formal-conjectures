/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor529Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor529Cell118
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (538283/65536)
  b := (1291879/131072)
  s := [(7655358351745/9007199254740992),(-2118099073277/4503599627370496),(136358836339/1125899906842624)]
  L := [(18931705534810452853/18446744073709551616),(-3949504585/412316860416),(8379647267/3298534883328),(-227456837/412316860416),(16008763/206158430208)]
  c := (1120157615427/1099511627776)
  R := (465082424907/50000000000000)
  total := (2256590104479/125000000000000)
  k := 0
  n := 32
  sFloor := (1127507723975/4503599627370496)
  nFloor := 584380193525756767158654730240
  eFloor := 568443387517852357593197969408
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1076566,width:=215313,den:=131072,localDen:=55340232221128654848,lowerC:=56379378804191133696,s:=[47034521713121280,-26027201412427776,6702309523734528],L:=[56795116604431358559,-530093532124282880,140587152202268672,-30528739880206336,4297319595900928],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor529Source.source.poly i) 1076566 215313 131072
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor529Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 8) (CoreQuotient.fused G u 4 8) (((44/23) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (44/23) 4 8 WideAnchor529Source.data
    WideAnchor529Source.path_checked WideAnchor529Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor529Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 8 4) (CoreQuotient.fused G u 8 4) (((44/23) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (44/23) 8 4 WideAnchor529Source.data
    WideAnchor529Source.path_swapped WideAnchor529Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor529Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor529Cell118
