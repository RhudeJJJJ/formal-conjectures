/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor282Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor282Cell031
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (583371/549755813888)
  b := (700045/549755813888)
  s := [(1099511627741/1099511627776),(-55/4398046511104),(-3/2199023255552)]
  L := [(3462857119059/151115727451828646838272),(4155421419583/453347182355485940514816),(69256904955/75557863725914323419136),(-13/28334198897217871282176),(1/4722366482869645213696)]
  c := (1731428559529/75557863725914323419136)
  R := (-1224960889095707/100000000000000)
  total := (-644956683/250000000000000)
  k := 36
  n := 32
  sFloor := (2199023255451/4398046511104)
  nFloor := (177849042043/4722366482869645213696)
  eFloor := (245777586405/9444732965739290427392)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=583371,width:=116674,den:=549755813888,localDen:=453347182355485940514816,lowerC:=10388571357174,s:=[453347182341054850400256,-5669356830720,-618475290624],L:=[10388571357177,4155421419583,415541429730,-208,96],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor282Source.source.poly i) 583371 116674 549755813888
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor282Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 8) (CoreQuotient.fused G u 0 8) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 8 WideAnchor282Source.data
    WideAnchor282Source.path_checked WideAnchor282Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor282Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 8 0) (CoreQuotient.fused G u 8 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 8 0 WideAnchor282Source.data
    WideAnchor282Source.path_swapped WideAnchor282Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor282Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor282Cell031
