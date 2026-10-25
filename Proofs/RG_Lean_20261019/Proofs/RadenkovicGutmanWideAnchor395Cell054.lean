/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor395Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor395Cell054
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (603851/8589934592)
  b := (724621/8589934592)
  s := [(1099511556619/1099511627776),(-28463/1099511627776),(-1423/549755813888)]
  L := [(460110164156496264588821669/10384593717069655257060992658440192),(1961564288539/110680464442257309696),(98078037665/55340232221128654848),(-725/13835058055282163712),(-1/432345564227567616)]
  c := (1634639673953/36893488147419103232)
  R := (-846606161165497/100000000000000)
  total := (-58855291551/500000000000000)
  k := 25
  n := 32
  sFloor := (549755762655/1099511627776)
  nFloor := (454152575439/4611686018427387904)
  eFloor := (1326712014273/18446744073709551616)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=603851,width:=120770,den:=8589934592,localDen:=31153781151208965771182977975320576,lowerC:=1380330492468704976782229504,s:=[31153779135032374841850911149522944,-806476303211512270304575488,-80639130061482061669072896],L:=[1380330492469488793766465007,552131262432969531099971584,55213026735165433949716480,-1632554864921804800,-72057594037927936],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor395Source.source.poly i) 603851 120770 8589934592
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor395Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 2) (CoreQuotient.fused G u 2 2) (((19/10) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (19/10) 2 2 WideAnchor395Source.data
    WideAnchor395Source.path_checked WideAnchor395Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor395Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 2) (CoreQuotient.fused G u 2 2) (((19/10) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (19/10) 2 2 WideAnchor395Source.data
    WideAnchor395Source.path_swapped WideAnchor395Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor395Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor395Cell054
