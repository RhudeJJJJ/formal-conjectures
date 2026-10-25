/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor249Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor249Cell022
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (904491/4398046511104)
  b := (1085389/4398046511104)
  s := [(2199023255551/2199023255552),(-3/4398046511104),(1/2199023255552)]
  L := [(3397184910243/9671406556917033397649408),(2038308692585/14507109835375550096474112),(12739415249/906694364710971881029632),(-1/113336795588871485128704),(1/226673591177742970257408)]
  c := (1698592455121/4835703278458516698824704)
  R := (-716931193736379/50000000000000)
  total := (-292956473/500000000000000)
  k := 42
  n := 32
  sFloor := (1099511627775/2199023255552)
  nFloor := (1011628468781/1208925819614629174706176)
  eFloor := (1108336426309/2417851639229258349412352)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=904491,width:=180898,den:=4398046511104,localDen:=29014219670751100192948224,lowerC:=10191554730726,s:=[29014219670737906053414912,-19791209299968,13194139533312],L:=[10191554730729,4076617385170,407661287968,-256,128],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor249Source.source.poly i) 904491 180898 4398046511104
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor249Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 2) (CoreQuotient.fused G u 0 2) (((36/19) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (36/19) 0 2 WideAnchor249Source.data
    WideAnchor249Source.path_checked WideAnchor249Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor249Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 0) (CoreQuotient.fused G u 2 0) (((36/19) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (36/19) 2 0 WideAnchor249Source.data
    WideAnchor249Source.path_swapped WideAnchor249Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor249Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor249Cell022
