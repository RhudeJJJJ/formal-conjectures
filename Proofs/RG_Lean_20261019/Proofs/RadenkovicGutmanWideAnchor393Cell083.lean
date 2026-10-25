/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor393Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor393Cell083
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (466597/33554432)
  b := (139979/8388608)
  s := [(1096612650317/1099511627776),(-4624421953/4398046511104),(-227379149/2199023255552)]
  L := [(643073789881299426989805/309485009821345068724781056),(1868122609941/2251799813685248),(278145572819/3377699720527872),(-17192915/140737488355328),(-1251767/211106232532992)]
  c := (292436102373/140737488355328)
  R := (-308820272999459/100000000000000)
  total := (-1665706529099/200000000000000)
  k := 9
  n := 32
  sFloor := (547671427627/1099511627776)
  nFloor := (642185605737/140737488355328)
  eFloor := (407969129191/140737488355328)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=466597,width:=93319,den:=33554432,localDen:=928455029464035206174343168,lowerC:=1929221369643637237874688,s:=[926007060625764981047033856,-976244296140691001573376,-96002311003895670767616],L:=[1929221369643898280969415,770258449403016910995456,76456072882226657755136,-113422859747186442240,-5505329487065120768],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor393Source.source.poly i) 466597 93319 33554432
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor393Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 2) (CoreQuotient.fused G u 2 2) (((56/29) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (56/29) 2 2 WideAnchor393Source.data
    WideAnchor393Source.path_checked WideAnchor393Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor393Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 2) (CoreQuotient.fused G u 2 2) (((56/29) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (56/29) 2 2 WideAnchor393Source.data
    WideAnchor393Source.path_swapped WideAnchor393Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor393Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor393Cell083
