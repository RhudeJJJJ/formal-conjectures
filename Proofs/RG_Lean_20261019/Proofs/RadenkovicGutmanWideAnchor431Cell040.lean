/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor431Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor431Cell040
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (376257/68719476736)
  b := (112877/17179869184)
  s := [(2199023253235/2199023255552),(-927/2199023255552),(-23/549755813888)]
  L := [(4390959938273/9444732965739290427392),(5269123914637/28334198897217871282176),(263454794713/14167099448608935641088),(-13/1770887431076116955136),(-1/885443715538058477568)]
  c := (137217498071/295147905179352825856)
  R := (-13430734498131/1250000000000)
  total := (-11663178667/1000000000000000)
  k := 32
  n := 32
  sFloor := (274877906527/549755813888)
  nFloor := (1624187519745/2361183241434822606848)
  eFloor := (920074579629/1180591620717411303424)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=376257,width:=75251,den:=68719476736,localDen:=28334198897217871282176,lowerC:=13172879814816,s:=[28334198867363553607680,-11944304050176,-1185410973696],L:=[13172879814819,5269123914637,526909589426,-208,-32],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor431Source.source.poly i) 376257 75251 68719476736
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor431Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 8) (CoreQuotient.fused G u 2 8) (((23/12) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (23/12) 2 8 WideAnchor431Source.data
    WideAnchor431Source.path_checked WideAnchor431Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor431Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 8 2) (CoreQuotient.fused G u 8 2) (((23/12) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (23/12) 8 2 WideAnchor431Source.data
    WideAnchor431Source.path_swapped WideAnchor431Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor431Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor431Cell040
