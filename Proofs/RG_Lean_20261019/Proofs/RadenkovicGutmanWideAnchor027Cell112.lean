/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor027Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor027Cell112
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (721081/262144)
  b := (865297/262144)
  s := [(1106658787727/70368744177664),(-999148354971/140737488355328),(54064813251/35184372088832)]
  L := [(21047505999042098559/18446744073709551616),(-24090971611/824633720832),(3475328615/1649267441664),(221391329/412316860416),(-1051427/6442450944)]
  c := (612567821039/549755813888)
  R := (2704636490611/50000000000000)
  total := (32925751435731/1000000000000000)
  k := 0
  n := 32
  sFloor := (1430428473487/281474976710656)
  nFloor := 1256876195545611431768747146755958939494886932480
  eFloor := 1067457217876084018991188029294250082797526974464
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=721081,width:=144216,den:=262144,localDen:=55340232221128654848,lowerC:=61663095889323884544,s:=[870311883749720064,-392881119548276736,85036598429220864],L:=[63142517997126295677,-1616717737470459904,116612677689671680,29714641177280512,-9031689158262784],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor027Source.source.poly i) 721081 144216 262144
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor027Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 36) (CoreQuotient.fused G u 9 36) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 36 WideAnchor027Source.data
    WideAnchor027Source.path_checked WideAnchor027Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor027Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 36 9) (CoreQuotient.fused G u 36 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 36 9 WideAnchor027Source.data
    WideAnchor027Source.path_swapped WideAnchor027Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor027Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor027Cell112
