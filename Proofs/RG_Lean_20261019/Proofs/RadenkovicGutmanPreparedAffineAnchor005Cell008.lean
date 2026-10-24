/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor005Source
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.PreparedAffineAnchor005Cell008
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
set_option profiler true
set_option profiler.threshold 100
def witness : ComputedPolynomialCell.Witness := {
  a := (4403/274877906944)
  b := (1352601/70368744177664)
  s := [(4398046511089/4398046511104),(-9/4398046511104),(1/2199023255552)]
  L := [(4289767381913/2417851639229258349412352),(1715902385793/2417851639229258349412352),(257384672935/3626777458843887524118528),(-7/151115727451828646838272),(5/226673591177742970257408)]
  c := (536220922739/302231454903657293676544)
  R := (-1352883400064389/100000000000000)
  total := (-21520317/500000000000000)
  k := 40
  n := 32
  sFloor := (2199023255541/4398046511104)
  nFloor := (34895251901/2417851639229258349412352)
  eFloor := (1068550330511/77371252455336267181195264)
}
noncomputable def affine0 : NestedInteger.Poly 1 := (rg_closed_integer_row% [IntegerPolynomialPaymentCell.affine (WideAnchor005Source.source.poly 0) 1127168 225433 70368744177664]).head!
theorem affine0_checked : affine0=IntegerPolynomialPaymentCell.affine (WideAnchor005Source.source.poly 0) 1127168 225433 70368744177664 := by decide +kernel
#print axioms affine0_checked
noncomputable def affine1 : NestedInteger.Poly 1 := (rg_closed_integer_row% [IntegerPolynomialPaymentCell.affine (WideAnchor005Source.source.poly 1) 1127168 225433 70368744177664]).head!
theorem affine1_checked : affine1=IntegerPolynomialPaymentCell.affine (WideAnchor005Source.source.poly 1) 1127168 225433 70368744177664 := by decide +kernel
#print axioms affine1_checked
noncomputable def affine2 : NestedInteger.Poly 1 := (rg_closed_integer_row% [IntegerPolynomialPaymentCell.affine (WideAnchor005Source.source.poly 2) 1127168 225433 70368744177664]).head!
theorem affine2_checked : affine2=IntegerPolynomialPaymentCell.affine (WideAnchor005Source.source.poly 2) 1127168 225433 70368744177664 := by decide +kernel
#print axioms affine2_checked
noncomputable def affine3 : NestedInteger.Poly 1 := (rg_closed_integer_row% [IntegerPolynomialPaymentCell.affine (WideAnchor005Source.source.poly 3) 1127168 225433 70368744177664]).head!
theorem affine3_checked : affine3=IntegerPolynomialPaymentCell.affine (WideAnchor005Source.source.poly 3) 1127168 225433 70368744177664 := by decide +kernel
#print axioms affine3_checked
noncomputable def affine4 : NestedInteger.Poly 1 := (rg_closed_integer_row% [IntegerPolynomialPaymentCell.affine (WideAnchor005Source.source.poly 4) 1127168 225433 70368744177664]).head!
theorem affine4_checked : affine4=IntegerPolynomialPaymentCell.affine (WideAnchor005Source.source.poly 4) 1127168 225433 70368744177664 := by decide +kernel
#print axioms affine4_checked
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1127168,width:=225433,den:=70368744177664,localDen:=7253554917687775048237056,lowerC:=12869302145736,s:=[7253554917663036036612096,-14843406974976,3298534883328],L:=[12869302145739,5147707157379,514769345870,-336,160],transformed:=![affine0,affine1,affine2,affine3,affine4]
}
theorem affine_checked : ∀ i, geometry.transformed i=IntegerPolynomialPaymentCell.affine (WideAnchor005Source.source.poly i) geometry.left geometry.width geometry.den := by
  intro i
  fin_cases i
  · exact affine0_checked
  · exact affine1_checked
  · exact affine2_checked
  · exact affine3_checked
  · exact affine4_checked
noncomputable def preparedMargin : NestedInteger.Poly 1 := (rg_closed_integer_row% [IntegerPolynomialPaymentCell.margin geometry]).head!
theorem margin_checked : preparedMargin=IntegerPolynomialPaymentCell.margin geometry := by decide +kernel
#print axioms margin_checked
theorem margin_sign : IntegerPolynomialPaymentCell.positive preparedMargin=true := by decide +kernel
#print axioms margin_sign
theorem margin_positive : IntegerPolynomialPaymentCell.positive (IntegerPolynomialPaymentCell.margin geometry)=true :=
  (congrArg IntegerPolynomialPaymentCell.positive margin_checked).symm.trans margin_sign
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor005Source.source witness geometry=true := by
  unfold IntegerPolynomialPaymentCell.checks
  rw [decide_eq_true_eq]
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,affine_checked,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,margin_positive⟩
theorem budget : SemanticPolynomialPaymentCell.Budget witness := by
  unfold SemanticPolynomialPaymentCell.Budget
  decide +kernel
theorem logarithm_checked : RationalLog.accepts witness.c witness.R witness.k witness.n=true := by decide +kernel
noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 14) (CoreQuotient.fused G u 9 14) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 14 WideAnchor005Source.data
    WideAnchor005Source.path_checked WideAnchor005Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor005Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 14 9) (CoreQuotient.fused G u 14 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 14 9 WideAnchor005Source.data
    WideAnchor005Source.path_swapped WideAnchor005Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor005Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.PreparedAffineAnchor005Cell008
