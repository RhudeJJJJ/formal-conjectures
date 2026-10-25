/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor505Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor505Cell052
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (838683/17179869184)
  b := (1006419/17179869184)
  s := [(4398033555125/4398046511104),(-1295585/1099511627776),(-129553/1099511627776)]
  L := [(1801026917349/1152921504606846976),(4322425712723/6917529027641081856),(216115827145/3458764513820540928),(-117131/432345564227567616),(-2929/216172782113783808)]
  c := (1801026917349/1152921504606846976)
  R := (-167118158822581/25000000000000)
  total := (-12870262143/200000000000000)
  k := 20
  n := 32
  sFloor := (1099506963643/2199023255552)
  nFloor := (31091083881/144115188075855872)
  eFloor := (234523533447/1152921504606846976)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=838683,width:=167736,den:=17179869184,localDen:=6917529027641081856,lowerC:=10806161504094,s:=[6917508649648128000,-8151116021760,-815076999168],L:=[10806161504094,4322425712723,432231654290,-1874096,-93728],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor505Source.source.poly i) 838683 167736 17179869184
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor505Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 35) (CoreQuotient.fused G u 4 35) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 4 35 WideAnchor505Source.data
    WideAnchor505Source.path_checked WideAnchor505Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor505Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 35 4) (CoreQuotient.fused G u 35 4) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 35 4 WideAnchor505Source.data
    WideAnchor505Source.path_swapped WideAnchor505Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor505Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor505Cell052
