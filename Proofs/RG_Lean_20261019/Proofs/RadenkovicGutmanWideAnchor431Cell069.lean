/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor431Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor431Cell069
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (581469/536870912)
  b := (1395525/1073741824)
  s := [(4397865229591/4398046511104),(-72508129/4398046511104),(-3624207/2199023255552)]
  L := [(5243287472271/288230376151711744),(6291787263589/864691128455135232),(314560258357/432345564227567616),(-707257/54043195528445952),(-17677/27021597764222976)]
  c := (1310821868067/72057594037927936)
  R := (-54572833373661/10000000000000)
  total := (-1161818217019/1000000000000000)
  k := 16
  n := 32
  sFloor := (549723184131/1099511627776)
  nFloor := (484903613381/18014398509481984)
  eFloor := (549369004839/18014398509481984)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1162938,width:=232587,den:=1073741824,localDen:=864691128455135232,lowerC:=15729862416804,s:=[864655487059427328,-14255678226432,-1425096179712],L:=[15729862416813,6291787263589,629120516714,-11316112,-565664],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor431Source.source.poly i) 1162938 232587 1073741824
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
end Gebendorfer.RadenkovicGutman.WideAnchor431Cell069
