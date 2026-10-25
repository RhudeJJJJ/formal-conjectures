/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor396Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor396Cell033
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (420027/274877906944)
  b := (15751/8589934592)
  s := [(4398046510971/4398046511104),(-53/4398046511104),(-3/2199023255552)]
  L := [(5916662575683/302231454903657293676544),(2366653761111/302231454903657293676544),(118332124627/151115727451828646838272),(-5/18889465931478580854784),(1/9444732965739290427392)]
  c := (92447852745/4722366482869645213696)
  R := (-154104290199553/12500000000000)
  total := (-14605469/3906250000000)
  k := 36
  n := 32
  sFloor := (68719476733/137438953472)
  nFloor := (1647559219549/37778931862957161709568)
  eFloor := (1272093363505/37778931862957161709568)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=420027,width:=84005,den:=274877906944,localDen:=302231454903657293676544,lowerC:=5916662575680,s:=[302231454894517603270656,-3642132267008,-412316860416],L:=[5916662575683,2366653761111,236664249254,-80,32],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor396Source.source.poly i) 420027 84005 274877906944
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor396Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 2) (CoreQuotient.fused G u 2 2) (((17/9) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (17/9) 2 2 WideAnchor396Source.data
    WideAnchor396Source.path_checked WideAnchor396Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor396Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 2) (CoreQuotient.fused G u 2 2) (((17/9) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (17/9) 2 2 WideAnchor396Source.data
    WideAnchor396Source.path_swapped WideAnchor396Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor396Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor396Cell033
