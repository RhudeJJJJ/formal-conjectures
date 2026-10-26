/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor427Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor427Cell119
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1291879/131072)
  b := (775127/65536)
  s := [(4505555113873/9007199254740992),(-2518219113085/9007199254740992),(326967155215/4503599627370496)]
  L := [(75169459187225639551/73786976294838206464),(-23022639937/3298534883328),(6287182919/3298534883328),(-44135491/103079215104),(12798493/206158430208)]
  c := (1114131222589/1099511627776)
  R := (660441108209/100000000000000)
  total := (3859334607211/250000000000000)
  k := 0
  n := 32
  sFloor := (1320635155609/9007199254740992)
  nFloor := 1799711995901943994122240
  eFloor := 1764845921638746031128576
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1291879,width:=258375,den:=131072,localDen:=221360928884514619392,lowerC:=224304242084636786688,s:=[110728522478542848,-61887752923176960,16071089613127680],L:=[225508377561676918653,-1545023212453101568,421925703454294016,-94780245218951168,13742277218271232],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor427Source.source.poly i) 1291879 258375 131072
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor427Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 6) (CoreQuotient.fused G u 2 6) (((28/15) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (28/15) 2 6 WideAnchor427Source.data
    WideAnchor427Source.path_checked WideAnchor427Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor427Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 6 2) (CoreQuotient.fused G u 6 2) (((28/15) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (28/15) 6 2 WideAnchor427Source.data
    WideAnchor427Source.path_swapped WideAnchor427Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor427Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor427Cell119
