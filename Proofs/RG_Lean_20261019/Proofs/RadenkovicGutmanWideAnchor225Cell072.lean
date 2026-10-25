/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor225Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor225Cell072
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (502389/268435456)
  b := (1205733/536870912)
  s := [(4397199437973/4398046511104),(-169351545/2199023255552),(-2112549/274877906944)]
  L := [(27800446862648960536445205/316912650057057350374175801344),(157991429631/4503599627370496),(11838722587/3377699720527872),(-353085/562949953421312),(-13181/422212465065984)]
  c := (1580272445531/18014398509481984)
  R := (-467066468412713/100000000000000)
  total := (-85659530331/50000000000000)
  k := 14
  n := 32
  sFloor := (2198413467049/4398046511104)
  nFloor := (184315074197/2251799813685248)
  eFloor := (809434222583/9007199254740992)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1004778,width:=200955,den:=536870912,localDen:=950737950171172051122527404032,lowerC:=83401340587936805120114688,s:=[950554836015789947474027741184,-73218389275835307361566720,-7306809514907069916905472],L:=[83401340587946881609335615,33352975481901728453885952,3332304164459742150787072,-596307552911291842560,-29680973344185253888],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor225Source.source.poly i) 1004778 200955 536870912
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor225Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 10) (CoreQuotient.fused G u 0 10) (((36/19) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (36/19) 0 10 WideAnchor225Source.data
    WideAnchor225Source.path_checked WideAnchor225Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor225Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 10 0) (CoreQuotient.fused G u 10 0) (((36/19) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (36/19) 10 0 WideAnchor225Source.data
    WideAnchor225Source.path_swapped WideAnchor225Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor225Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor225Cell072
