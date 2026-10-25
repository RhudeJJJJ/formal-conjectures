/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor231Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor231Cell066
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (672997/1073741824)
  b := (201899/268435456)
  s := [(4397680608341/4398046511104),(-146332945/4398046511104),(-7308933/2199023255552)]
  L := [(160555833959252995793067599/5070602400912917605986812821504),(2737569266447/216172782113783808),(45600333109/36028797018963968),(-1925813/13510798882111488),(-16013/2251799813685248)]
  c := (285204453759/9007199254740992)
  R := (-16188013168823/3125000000000)
  total := (-79701498487/125000000000000)
  k := 15
  n := 32
  sFloor := (2198759828765/4398046511104)
  nFloor := (716287216921/72057594037927936)
  eFloor := (470527069169/36028797018963968)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=672997,width:=134599,den:=1073741824,localDen:=15211807202738752817960438464512,lowerC:=481667501877539346447335424,s:=[15210541631246579530348728680448,-506131197368852955487272960,-50559756188583815333019648],L:=[481667501877758987379202797,192639311379244238722039808,19253029049780896064864256,-2168272677296314253312,-108174211249625628672],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor231Source.source.poly i) 672997 134599 1073741824
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor231Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 14) (CoreQuotient.fused G u 0 14) (((17/9) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (17/9) 0 14 WideAnchor231Source.data
    WideAnchor231Source.path_checked WideAnchor231Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor231Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 14 0) (CoreQuotient.fused G u 14 0) (((17/9) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (17/9) 14 0 WideAnchor231Source.data
    WideAnchor231Source.path_swapped WideAnchor231Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor231Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor231Cell066
