/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor433Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor433Cell053
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1006419/17179869184)
  b := (603851/8589934592)
  s := [(4398045667013/4398046511104),(-337637/4398046511104),(-16881/2199023255552)]
  L := [(115204164165192384604474987/2596148429267413814265248164610048),(491142872131/27670116110564327424),(16371354971/9223372036854775808),(-1345/6917529027641081856),(-3/288230376151711744)]
  c := (1637149639537/36893488147419103232)
  R := (-423264722885539/50000000000000)
  total := (-196166009/2000000000000)
  k := 25
  n := 32
  sFloor := (2199022647807/4398046511104)
  nFloor := (370065060083/9223372036854775808)
  eFloor := (3126071435/36028797018963968)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1006419,width:=201283,den:=17179869184,localDen:=7788445287802241442795744493830144,lowerC:=345612492495401955260104704,s:=[7788443793012098858325107716128768,-597917119566246900381253632,-59788701447991860639301632],L:=[345612492495577153813424961,138244428494677922793127936,13824380277552322002812928,-1514335374703329280,-81064793292668928],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor433Source.source.poly i) 1006419 201283 17179869184
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor433Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 8) (CoreQuotient.fused G u 2 8) (((13/7) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (13/7) 2 8 WideAnchor433Source.data
    WideAnchor433Source.path_checked WideAnchor433Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor433Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 8 2) (CoreQuotient.fused G u 8 2) (((13/7) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (13/7) 8 2 WideAnchor433Source.data
    WideAnchor433Source.path_swapped WideAnchor433Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor433Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor433Cell053
