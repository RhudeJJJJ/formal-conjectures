/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor243Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor243Cell133
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (518331/4096)
  b := 128
  s := [(4550556842977/18446744073709551616),(-156840209079/18446744073709551616),(1751850149/9223372036854775808)]
  L := [(619047005956307401989111553/618970019642690137449562112),(-1568301/549755813888),(53955/1099511627776),(-13/17179869184),(1/68719476736)]
  c := (1099645299477/1099511627776)
  R := (6078315717/100000000000000)
  total := (17882685237/200000000000000)
  k := 0
  n := 32
  sFloor := (1099305083549/9223372036854775808)
  nFloor := 170978502140547761041919990354409782852050580945582535868680600058398991349202589594498809019870738514983335421122885713920
  eFloor := 170957154458884369401987089365582015126665913200218736719908600980854594734907225823583822744438633695165397724587412684800
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=518331,width:=5957,den:=4096,localDen:=618970019642690137449562112,lowerC:=619045270120541834994253824,s:=[152691350149806424064,-5262684130407088128,117564673397620736],L:=[619047005956307401989111553,-1765749949801194061824,30373964736846888960,-468374361246531584,9007199254740992],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor243Source.source.poly i) 518331 5957 4096
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor243Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 25) (CoreQuotient.fused G u 0 25) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 25 WideAnchor243Source.data
    WideAnchor243Source.path_checked WideAnchor243Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor243Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 25 0) (CoreQuotient.fused G u 25 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 25 0 WideAnchor243Source.data
    WideAnchor243Source.path_swapped WideAnchor243Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor243Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor243Cell133
