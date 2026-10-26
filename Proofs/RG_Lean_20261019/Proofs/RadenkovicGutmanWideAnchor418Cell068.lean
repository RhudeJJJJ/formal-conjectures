/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor418Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor418Cell068
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (969115/1073741824)
  b := (581469/536870912)
  s := [(4397980693481/4398046511104),(-26326599/4398046511104),(-1316205/2199023255552)]
  L := [(168661249928403606820848605/20282409603651670423947251286016),(2876165128577/864691128455135232),(47934785907/144115188075855872),(-97481/54043195528445952),(-811/9007199254740992)]
  c := (74900641213/9007199254740992)
  R := (-584868614066147/100000000000000)
  total := (-1038836804909/1000000000000000)
  k := 17
  n := 32
  sFloor := (549743966809/1099511627776)
  nFloor := (298644283463/18014398509481984)
  eFloor := (537457422477/36028797018963968)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=969115,width:=193823,den:=1073741824,localDen:=60847228810955011271841753858048,lowerC:=505983749785017023276777472,s:=[60846318220319745597231933161472,-364230025563133355898175488,-36419545175305320577105920],L:=[505983749785210820462545815,202392128145552998691504128,20238664120204659668287488,-109753848818925830144,-5478628946696208384],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor418Source.source.poly i) 969115 193823 1073741824
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor418Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 4) (CoreQuotient.fused G u 2 4) (((40/21) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (40/21) 2 4 WideAnchor418Source.data
    WideAnchor418Source.path_checked WideAnchor418Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor418Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 2) (CoreQuotient.fused G u 4 2) (((40/21) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (40/21) 4 2 WideAnchor418Source.data
    WideAnchor418Source.path_swapped WideAnchor418Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor418Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor418Cell068
