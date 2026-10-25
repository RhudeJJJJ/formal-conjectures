/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor284Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor284Cell102
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (931671/2097152)
  b := (1118005/2097152)
  s := [(5479722566527/17592186044416),(-915101276733/17592186044416),(45986632349/8796093022208)]
  L := [(14347803772749465159/18446744073709551616),(3053650641919/26388279066624),(-166407823859/13194139533312),(1340240975/1649267441664),(-25801561/824633720832)]
  c := (1710391494363/2199023255552)
  R := (-12564549932321/100000000000000)
  total := (-1027329385891/125000000000000)
  k := 1
  n := 32
  sFloor := (1164148638623/8796093022208)
  nFloor := (515599348453/4294967296)
  eFloor := (174006552607/2147483648)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=931671,width:=186334,den:=2097152,localDen:=55340232221128654848,lowerC:=43043411318236250112,s:=[17237716709755846656,-2878659709054746624,289322874011910144],L:=[43043411318248395477,6403969551001714688,-697965001243099136,44971024659251200,-1731513448136704],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor284Source.source.poly i) 931671 186334 2097152
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor284Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 8) (CoreQuotient.fused G u 0 8) (((13/7) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (13/7) 0 8 WideAnchor284Source.data
    WideAnchor284Source.path_checked WideAnchor284Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor284Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 8 0) (CoreQuotient.fused G u 8 0) (((13/7) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (13/7) 8 0 WideAnchor284Source.data
    WideAnchor284Source.path_swapped WideAnchor284Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor284Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor284Cell102
