/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor251Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor251Cell047
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (674097/34359738368)
  b := (202229/8589934592)
  s := [(2199023248033/2199023255552),(-47/34359738368),(-75/549755813888)]
  L := [(6559366706765/2361183241434822606848),(7871216677877/7083549724304467820544),(393559662785/3541774862152233910272),(-71/442721857769029238784),(-5/221360928884514619392)]
  c := (1639841676691/590295810358705651712)
  R := (-985076732206739/100000000000000)
  total := (-38284159909/1000000000000000)
  k := 29
  n := 32
  sFloor := (2199023244725/4398046511104)
  nFloor := (484215329891/73786976294838206464)
  eFloor := (37247754063/9223372036854775808)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=674097,width:=134819,den:=34359738368,localDen:=7083549724304467820544,lowerC:=19678100120292,s:=[7083549700084073496576,-9689446219776,-966367641600],L:=[19678100120295,7871216677877,787119325570,-1136,-160],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor251Source.source.poly i) 674097 134819 34359738368
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor251Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 2) (CoreQuotient.fused G u 0 2) (((13/7) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (13/7) 0 2 WideAnchor251Source.data
    WideAnchor251Source.path_checked WideAnchor251Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor251Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 0) (CoreQuotient.fused G u 2 0) (((13/7) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (13/7) 2 0 WideAnchor251Source.data
    WideAnchor251Source.path_swapped WideAnchor251Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor251Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor251Cell047
