/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor266Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor266Cell057
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (521727/4294967296)
  b := (78259/536870912)
  s := [(2198981727957/2199023255552),(-33220387/4398046511104),(-1660581/2199023255552)]
  L := [(175489668889478948134844761/20282409603651670423947251286016),(5985007908721/1729382256910270464),(299203490281/864691128455135232),(-1143841/108086391056891904),(-28585/54043195528445952)]
  c := (1246929094303/144115188075855872)
  R := (-291442109298279/50000000000000)
  total := (-34833238441/250000000000000)
  k := 17
  n := 32
  sFloor := (1099481728591/2199023255552)
  nFloor := (696067923663/576460752303423488)
  eFloor := (759627498199/576460752303423488)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=521727,width:=104345,den:=4294967296,localDen:=60847228810955011271841753858048,lowerC:=526469006668164456253489152,s:=[60846079737579568781231042592768,-459605982763940872709996544,-45948469080997021398073344],L:=[526469006668436844404534283,210578745215041930759503872,21054573864647865961283584,-643925237671386939392,-32183848837096407040],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor266Source.source.poly i) 521727 104345 4294967296
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor266Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 42) (CoreQuotient.fused G u 0 42) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 42 WideAnchor266Source.data
    WideAnchor266Source.path_checked WideAnchor266Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor266Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 42 0) (CoreQuotient.fused G u 42 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 42 0 WideAnchor266Source.data
    WideAnchor266Source.path_swapped WideAnchor266Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor266Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor266Cell057
