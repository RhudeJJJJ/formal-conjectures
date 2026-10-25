/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor015Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor015Cell070
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1395525/1073741824)
  b := (837315/536870912)
  s := [(4280630905585/4398046511104),(-11270152627/1099511627776),(-1772542955/2199023255552)]
  L := [(1080532704040272377827/75557863725914323419136),(97749785123/17592186044416),(51973281173/105553116266496),(-104027137/8796093022208),(-1090801/3298534883328)]
  c := (1006324499883/70368744177664)
  R := (-106186115141703/50000000000000)
  total := (-105689966261/200000000000000)
  k := 7
  n := 32
  sFloor := (2116002604583/4398046511104)
  nFloor := (147963012903/1125899906842624)
  eFloor := (559921553487/4503599627370496)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1395525,width:=279105,den:=1073741824,localDen:=226673591177742970257408,lowerC:=3241598112120780619776,s:=[220622036948813264977920,-2323436973786887356416,-182712336539524792320],L:=[3241598112120817133481,1259496390882937012224,111611771451923759104,-2680758907869069312,-74959273943105536],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor015Source.source.poly i) 1395525 279105 1073741824
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor015Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 24) (CoreQuotient.fused G u 9 24) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 24 WideAnchor015Source.data
    WideAnchor015Source.path_checked WideAnchor015Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor015Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 24 9) (CoreQuotient.fused G u 24 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 24 9 WideAnchor015Source.data
    WideAnchor015Source.path_swapped WideAnchor015Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor015Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor015Cell070
