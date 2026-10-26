/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor036Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor036Cell014
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (841425/17592186044416)
  b := (504855/8796093022208)
  s := [(1099511627763/1099511627776),(-21/4398046511104),(-1/2199023255552)]
  L := [(469879471565/75557863725914323419136),(751807154493/302231454903657293676544),(18795178861/75557863725914323419136)]
  c := (469879471565/75557863725914323419136)
  R := (-645086091681783/50000000000000)
  total := (-122519879/1000000000000000)
  k := 38
  n := 32
  sFloor := (1099511627757/2199023255552)
  nFloor := (337213748933/2417851639229258349412352)
  eFloor := (319632486157/2417851639229258349412352)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=841425,width:=168285,den:=17592186044416,localDen:=302231454903657293676544,lowerC:=1879517886260,s:=[302231454900083880886272,-1443109011456,-137438953472],L:=[1879517886260,751807154493,75180715444],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor036Source.source.poly i) 841425 168285 17592186044416
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor036Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 10 15) (CoreQuotient.fused G u 10 15) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 10 15 WideAnchor036Source.data
    WideAnchor036Source.path_checked WideAnchor036Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor036Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 15 10) (CoreQuotient.fused G u 15 10) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 15 10 WideAnchor036Source.data
    WideAnchor036Source.path_swapped WideAnchor036Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor036Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor036Cell014
