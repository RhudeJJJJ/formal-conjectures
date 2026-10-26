/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor282Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor282Cell094
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (433355/4194304)
  b := (260013/2097152)
  s := [(3487015649757/4398046511104),(-510559819031/8796093022208),(7005496987/4398046511104)]
  L := [(50577249182353456923/295147905179352825856),(1447458875537/26388279066624),(2228174399/1649267441664),(-358178473/824633720832),(13669939/412316860416)]
  c := (1507319485615/8796093022208)
  R := (-88198737495107/100000000000000)
  total := (-417710639109/25000000000000)
  k := 3
  n := 32
  sFloor := (809685309307/2199023255552)
  nFloor := (2059014736069/4398046511104)
  eFloor := (1388263530705/4398046511104)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=433355,width:=86671,den:=4194304,localDen:=885443715538058477568,lowerC:=151731747547030487040,s:=[702028977016242438144,-51394634188823986176,1410392833658978304],L:=[151731747547060370769,48568660412002729984,1196242021686181888,-384591206916554752,29355970471657472],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor282Source.source.poly i) 433355 86671 4194304
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor282Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 8) (CoreQuotient.fused G u 0 8) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 8 WideAnchor282Source.data
    WideAnchor282Source.path_checked WideAnchor282Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor282Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 8 0) (CoreQuotient.fused G u 8 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 8 0 WideAnchor282Source.data
    WideAnchor282Source.path_swapped WideAnchor282Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor282Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor282Cell094
