/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor032Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor032Cell073
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1205733/536870912)
  b := (1446879/536870912)
  s := [(2107166576085/2199023255552),(-68677153157/4398046511104),(-2267247151/2199023255552)]
  L := [(1693958096255974939899/75557863725914323419136),(600969634029/70368744177664),(36559799513/52776558133248),(-126776587/4398046511104),(-1443221/3298534883328)]
  c := (1577621415495/70368744177664)
  R := (-47472886379053/25000000000000)
  total := (-50816977669/62500000000000)
  k := 6
  n := 32
  sFloor := (2070560752355/4398046511104)
  nFloor := (1191012423853/4503599627370496)
  eFloor := (141651402225/562949953421312)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1205733,width:=241146,den:=536870912,localDen:=226673591177742970257408,lowerC:=5081874288765189488640,s:=[217205076756224897187840,-3539593521500377841664,-233706056771860168704],L:=[5081874288767924819697,1935858693032732786688,157023143256651726848,-6534015540761985024,-99177391934406656],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor032Source.source.poly i) 1205733 241146 536870912
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor032Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 10 11) (CoreQuotient.fused G u 10 11) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 10 11 WideAnchor032Source.data
    WideAnchor032Source.path_checked WideAnchor032Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor032Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 11 10) (CoreQuotient.fused G u 11 10) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 11 10 WideAnchor032Source.data
    WideAnchor032Source.path_swapped WideAnchor032Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor032Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor032Cell073
