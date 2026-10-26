/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor526Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor526Cell129
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (249967/4096)
  b := (1199841/16384)
  s := [(5066753205435/2305843009213693952),(-5806953099441/4611686018427387904),(769911474809/2305843009213693952)]
  L := [(590609858449799521951/590295810358705651712),(-2792373373/13194139533312),(413541827/6597069766656),(-12671051/824633720832),(985693/412316860416)]
  c := (549959273783/549755813888)
  R := (9250573153/50000000000000)
  total := (1353674323021/500000000000000)
  k := 0
  n := 32
  sFloor := (1466594065261/2305843009213693952)
  nFloor := 199034167876635638526114673942316162678677196242944
  eFloor := 198927459720095153907129999904518491326555740962816
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=999868,width:=199973,den:=16384,localDen:=1770887431076116955136,lowerC:=1771542821272421400576,s:=[3891266461774080,-2229869990185344,591292012653312],L:=[1771829575349398565853,-374786009851756544,111009288905818112,-27210874825474048,4233519198896128],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor526Source.source.poly i) 999868 199973 16384
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor526Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 6) (CoreQuotient.fused G u 4 6) (((13/7) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (13/7) 4 6 WideAnchor526Source.data
    WideAnchor526Source.path_checked WideAnchor526Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor526Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 6 4) (CoreQuotient.fused G u 6 4) (((13/7) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (13/7) 6 4 WideAnchor526Source.data
    WideAnchor526Source.path_swapped WideAnchor526Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor526Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor526Cell129
