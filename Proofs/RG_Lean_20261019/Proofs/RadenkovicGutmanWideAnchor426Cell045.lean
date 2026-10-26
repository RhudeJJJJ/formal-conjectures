/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor426Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor426Cell045
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (468123/34359738368)
  b := (1123495/68719476736)
  s := [(549755811073/549755813888),(-9011/4398046511104),(-449/2199023255552)]
  L := [(4205803358157/2361183241434822606848),(5046958633963/7083549724304467820544),(252347661143/3541774862152233910272),(-31/442721857769029238784),(1/221360928884514619392)]
  c := (1051450839539/590295810358705651712)
  R := (-125912271127107/12500000000000)
  total := (-27191773649/1000000000000000)
  k := 30
  n := 32
  sFloor := (2199023239337/4398046511104)
  nFloor := (1650213157751/590295810358705651712)
  eFloor := (296488587261/73786976294838206464)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=936246,width:=187249,den:=68719476736,localDen:=7083549724304467820544,lowerC:=12617410074468,s:=[7083549688033469005824,-14513231364096,-1446330236928],L:=[12617410074471,5046958633963,504695322286,-496,32],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor426Source.source.poly i) 936246 187249 68719476736
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor426Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 6) (CoreQuotient.fused G u 2 6) (((15/8) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (15/8) 2 6 WideAnchor426Source.data
    WideAnchor426Source.path_checked WideAnchor426Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor426Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 6 2) (CoreQuotient.fused G u 6 2) (((15/8) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (15/8) 6 2 WideAnchor426Source.data
    WideAnchor426Source.path_swapped WideAnchor426Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor426Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor426Cell045
