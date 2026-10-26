/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor036Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor036Cell080
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1080087/134217728)
  b := (162013/16777216)
  s := [(3456475698455/4398046511104),(-122771603425/2199023255552),(86100069/34359738368)]
  L := [(149377700777968676933/1180591620717411303424),(324345402105/8796093022208),(-4595130169/26388279066624),(-88709097/274877906944),(57471529/1649267441664)]
  c := (1112950599029/8796093022208)
  R := (-103364648112973/100000000000000)
  total := (-1557048902641/1000000000000000)
  k := 3
  n := 32
  sFloor := (805488325109/2199023255552)
  nFloor := (560870383623/140737488355328)
  eFloor := (265692703933/70368744177664)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1080087,width:=216017,den:=134217728,localDen:=3541774862152233910272,lowerC:=448133102333734158336,s:=[2783521890803059261440,-197737508095446220800,8875127532920242176],L:=[448133102333906030799,130598708873338552320,-616747931147436032,-1143008011418075136,123419168753057792],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor036Source.source.poly i) 1080087 216017 134217728
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor036Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 10 15) (CoreQuotient.fused G u 10 15) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 10 15 WideAnchor036Source.data
    WideAnchor036Source.path_checked WideAnchor036Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor036Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 15 10) (CoreQuotient.fused G u 15 10) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 15 10 WideAnchor036Source.data
    WideAnchor036Source.path_swapped WideAnchor036Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor036Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor036Cell080
