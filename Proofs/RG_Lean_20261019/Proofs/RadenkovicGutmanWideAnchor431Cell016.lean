/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor431Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor431Cell016
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (302913/4398046511104)
  b := (726991/8796093022208)
  s := [(4398046511103/4398046511104),(1/4398046511104),(-1/2199023255552)]
  L := [(2845942508241/38685626227668133590597632),(3415125372733/116056878683004400771792896),(7114832783/2417851639229258349412352),(-1/7253554917687775048237056)]
  c := (177871406765/2417851639229258349412352)
  R := (-302405949331027/20000000000000)
  total := (-206988917/1000000000000000)
  k := 44
  n := 32
  sFloor := (2199023255551/4398046511104)
  nFloor := (65793476245/604462909807314587353088)
  eFloor := (298167073895/2417851639229258349412352)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=605826,width:=121165,den:=8796093022208,localDen:=116056878683004400771792896,lowerC:=8537827524720,s:=[116056878682978012492726272,26388279066624,-52776558133248],L:=[8537827524723,3415125372733,341511973584,-16],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor431Source.source.poly i) 605826 121165 8796093022208
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor431Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 8) (CoreQuotient.fused G u 2 8) (((23/12) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (23/12) 2 8 WideAnchor431Source.data
    WideAnchor431Source.path_checked WideAnchor431Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor431Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 8 2) (CoreQuotient.fused G u 8 2) (((23/12) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (23/12) 8 2 WideAnchor431Source.data
    WideAnchor431Source.path_swapped WideAnchor431Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor431Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor431Cell016
