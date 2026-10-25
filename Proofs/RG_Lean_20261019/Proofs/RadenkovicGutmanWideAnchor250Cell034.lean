/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor250Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor250Cell034
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (15751/8589934592)
  b := (302419/137438953472)
  s := [(4398046510971/4398046511104),(-27/2199023255552),(-1/1099511627776)]
  L := [(68977627364532699893233971/2658455991569831745807614120560689152),(1568363442385/151115727451828646838272),(235253582969/226673591177742970257408),(-9/9444732965739290427392),(7/14167099448608935641088)]
  c := (1960462082153/75557863725914323419136)
  R := (-48749968809941/4000000000000)
  total := (-2217572873/500000000000000)
  k := 36
  n := 32
  sFloor := (68719476733/137438953472)
  nFloor := (582105297723/9444732965739290427392)
  eFloor := (1352931599659/37778931862957161709568)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=252016,width:=50403,den:=137438953472,localDen:=7975367974709495237422842361682067456,lowerC:=206932882093552441793445888,s:=[7975367974468314536409723841328185344,-97922991388784963151200256,-7253554917687775048237056],L:=[206932882093598099679701913,82772824391092902800916480,8277249598412206750302208,-7599824371187712,3940649673949184],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor250Source.source.poly i) 252016 50403 137438953472
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor250Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 2) (CoreQuotient.fused G u 0 2) (((15/8) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (15/8) 0 2 WideAnchor250Source.data
    WideAnchor250Source.path_checked WideAnchor250Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor250Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 0) (CoreQuotient.fused G u 2 0) (((15/8) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (15/8) 2 0 WideAnchor250Source.data
    WideAnchor250Source.path_swapped WideAnchor250Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor250Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor250Cell034
