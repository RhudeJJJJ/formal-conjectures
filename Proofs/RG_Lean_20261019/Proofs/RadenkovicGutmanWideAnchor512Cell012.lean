/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor512Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor512Cell012
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (584323/17592186044416)
  b := (1402375/35184372088832)
  s := [(4398046511097/4398046511104),(-1/1099511627776)]
  L := [(2697392155687/4835703278458516698824704),(202304238565/906694364710971881029632),(20230406549/906694364710971881029632),(-7/906694364710971881029632),(1/226673591177742970257408)]
  c := (1348696077843/2417851639229258349412352)
  R := (-1410738112599623/100000000000000)
  total := (-93092357/1000000000000000)
  k := 41
  n := 32
  sFloor := (1099511627773/2199023255552)
  nFloor := (731915080153/9671406556917033397649408)
  eFloor := (1037020613987/9671406556917033397649408)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1168646,width:=233729,den:=35184372088832,localDen:=14507109835375550096474112,lowerC:=8092176467058,s:=[14507109835352460352290816,-13194139533312],L:=[8092176467061,3236867817040,323686504784,-112,64],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor512Source.source.poly i) 1168646 233729 35184372088832
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor512Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 42) (CoreQuotient.fused G u 4 42) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 4 42 WideAnchor512Source.data
    WideAnchor512Source.path_checked WideAnchor512Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor512Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 42 4) (CoreQuotient.fused G u 42 4) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 42 4 WideAnchor512Source.data
    WideAnchor512Source.path_swapped WideAnchor512Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor512Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor512Cell012
