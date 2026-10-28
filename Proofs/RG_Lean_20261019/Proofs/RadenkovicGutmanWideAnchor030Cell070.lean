/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor030Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor030Cell070
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1395525/1073741824)
  b := (837315/536870912)
  s := [(239807337329/274877906944),(-183181767707/4398046511104),(-670026355/1099511627776)]
  L := [(952199732109107121661/9444732965739290427392),(3695555864971/105553116266496),(90349424033/52776558133248),(-1636913719/6597069766656),(31126615/3298534883328)]
  c := (110850638257/1099511627776)
  R := (-114721884578087/100000000000000)
  total := (-11094836861/40000000000000)
  k := 4
  n := 32
  sFloor := (456381940517/1099511627776)
  nFloor := (1139337815419/4503599627370496)
  eFloor := (770043457501/4503599627370496)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1395525,width:=279105,den:=1073741824,localDen:=28334198897217871282176,lowerC:=2856599196327248658432,s:=[24719152108053479817216,-1180139552287550865408,-17266447693098516480],L:=[2856599196327321364983,992018223786964811776,48505977679271428096,-7030490889478733824,267375586920366080],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor030Source.source.poly i) 1395525 279105 1073741824
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor030Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 39) (CoreQuotient.fused G u 9 39) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 39 WideAnchor030Source.data
    WideAnchor030Source.path_checked WideAnchor030Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor030Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 39 9) (CoreQuotient.fused G u 39 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 39 9 WideAnchor030Source.data
    WideAnchor030Source.path_swapped WideAnchor030Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor030Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor030Cell070
