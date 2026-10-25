/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor377Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor377Cell028
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (337599/549755813888)
  b := (1620475/2199023255552)
  s := [(2199023255431/2199023255552),(-47/2199023255552),(-3/1099511627776)]
  L := [(306396846741/18889465931478580854784),(980469183433/151115727451828646838272),(147070268533/226673591177742970257408),(1/9444732965739290427392),(-1/14167099448608935641088)]
  c := (306396846741/18889465931478580854784)
  R := (-1242237218899567/100000000000000)
  total := (-302835061/200000000000000)
  k := 36
  n := 32
  sFloor := (1099511627689/2199023255552)
  nFloor := (628291591385/75557863725914323419136)
  eFloor := (1062206732731/75557863725914323419136)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1350396,width:=270079,den:=2199023255552,localDen:=453347182355485940514816,lowerC:=7353524321784,s:=[453347182330540770459648,-9689446219776,-1236950581248],L:=[7353524321784,2941407550299,294140537066,48,-32],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor377Source.source.poly i) 1350396 270079 2199023255552
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor377Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 14) (CoreQuotient.fused G u 2 14) (((40/21) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (40/21) 2 14 WideAnchor377Source.data
    WideAnchor377Source.path_checked WideAnchor377Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor377Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 14 2) (CoreQuotient.fused G u 14 2) (((40/21) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (40/21) 14 2 WideAnchor377Source.data
    WideAnchor377Source.path_swapped WideAnchor377Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor377Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor377Cell028
