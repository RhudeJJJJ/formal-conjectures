/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor266Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor266Cell036
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1451611/549755813888)
  b := (435483/137438953472)
  s := [(4398046471859/4398046511104),(-3925/1099511627776),(-49/137438953472)]
  L := [(2413305137379/590295810358705651712),(180997133909/110680464442257309696),(144797098159/885443715538058477568),(-65/27670116110564327424),(-7/55340232221128654848)]
  c := (1206652568689/295147905179352825856)
  R := (-965756855422667/100000000000000)
  total := (-5050574263/1000000000000000)
  k := 28
  n := 32
  sFloor := (2199023227295/4398046511104)
  nFloor := (1347108613559/2361183241434822606848)
  eFloor := (735059142253/1180591620717411303424)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1451611,width:=290321,den:=549755813888,localDen:=1770887431076116955136,lowerC:=7239915412134,s:=[1770887415273992749056,-6321654988800,-631360192512],L:=[7239915412137,2895954142544,289594196318,-4160,-224],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor266Source.source.poly i) 1451611 290321 549755813888
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
end Gebendorfer.RadenkovicGutman.WideAnchor266Cell036
