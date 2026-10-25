/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor250Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor250Cell026
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (937775/2199023255552)
  b := (562665/1099511627776)
  s := [(549755813887/549755813888),(-1/4398046511104),(-1/2199023255552)]
  L := [(6786401168987/4835703278458516698824704),(2714560467575/4835703278458516698824704),(135728023411/2417851639229258349412352),(-5/302231454903657293676544),(1/151115727451828646838272)]
  c := (848300146123/604462909807314587353088)
  R := (-341151586352771/25000000000000)
  total := (-5779401/5000000000000)
  k := 40
  n := 32
  sFloor := (1099511627773/2199023255552)
  nFloor := (2015035184179/604462909807314587353088)
  eFloor := (585419164231/302231454903657293676544)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=937775,width:=187555,den:=2199023255552,localDen:=4835703278458516698824704,lowerC:=6786401168984,s:=[4835703278449720605802496,-1099511627776,-2199023255552],L:=[6786401168987,2714560467575,271456046822,-80,32],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor250Source.source.poly i) 937775 187555 2199023255552
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor250Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 2) (CoreQuotient.fused G u 0 2) (((15/8) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (15/8) 0 2 WideAnchor250Source.data
    WideAnchor250Source.path_checked WideAnchor250Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor250Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 0) (CoreQuotient.fused G u 2 0) (((15/8) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (15/8) 2 0 WideAnchor250Source.data
    WideAnchor250Source.path_swapped WideAnchor250Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor250Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor250Cell026
