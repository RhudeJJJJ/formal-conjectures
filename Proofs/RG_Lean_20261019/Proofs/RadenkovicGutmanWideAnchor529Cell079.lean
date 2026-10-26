/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor529Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor529Cell079
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (900073/134217728)
  b := (1080087/134217728)
  s := [(2194969668143/2199023255552),(-808711725/1099511627776),(-39882357/549755813888)]
  L := [(1474847648407072722923923/2475880078570760549798248448),(804767960089/3377699720527872),(26818851481/1125899906842624),(-1031665/844424930131968),(-2641/35184372088832)]
  c := (335341530537/562949953421312)
  R := (-185644912596419/50000000000000)
  total := (-4854066111737/1000000000000000)
  k := 11
  n := 32
  sFloor := (2193192715265/4398046511104)
  nFloor := (121711049729/140737488355328)
  eFloor := (188491878485/140737488355328)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=900073,width:=180014,den:=134217728,localDen:=7427640235712281649394745344,lowerC:=4424542945219584976748544,s:=[7413948434653767048621981696,-5463170735040226551398400,-538842504371571278217216],L:=[4424542945221218168771769,1769703459558854783664128,176925834281742590017536,-9074621307756216320,-557531560119631872],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor529Source.source.poly i) 900073 180014 134217728
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor529Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 8) (CoreQuotient.fused G u 4 8) (((44/23) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (44/23) 4 8 WideAnchor529Source.data
    WideAnchor529Source.path_checked WideAnchor529Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor529Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 8 4) (CoreQuotient.fused G u 8 4) (((44/23) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (44/23) 8 4 WideAnchor529Source.data
    WideAnchor529Source.path_swapped WideAnchor529Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor529Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor529Cell079
