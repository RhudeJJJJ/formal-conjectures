/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor269Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor269Cell013
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1402375/35184372088832)
  b := (841425/17592186044416)
  s := [(4398046511097/4398046511104),(-1/4398046511104),(-1/2199023255552)]
  L := [(3890312247789/4835703278458516698824704),(583546837165/1813388729421943762059264),(116709367451/3626777458843887524118528),(-1/113336795588871485128704),(1/226673591177742970257408)]
  c := (972578061947/1208925819614629174706176)
  R := (-139242791331119/10000000000000)
  total := (-22050259/200000000000000)
  k := 41
  n := 32
  sFloor := (2199023255547/4398046511104)
  nFloor := (102644403669/604462909807314587353088)
  eFloor := (372912848143/2417851639229258349412352)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1402375,width:=280475,den:=35184372088832,localDen:=14507109835375550096474112,lowerC:=11670936743364,s:=[14507109835352460352290816,-3298534883328,-6597069766656],L:=[11670936743367,4668374697320,466837469804,-128,64],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor269Source.source.poly i) 1402375 280475 35184372088832
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor269Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 45) (CoreQuotient.fused G u 0 45) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 45 WideAnchor269Source.data
    WideAnchor269Source.path_checked WideAnchor269Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor269Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 45 0) (CoreQuotient.fused G u 45 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 45 0 WideAnchor269Source.data
    WideAnchor269Source.path_swapped WideAnchor269Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor269Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor269Cell013
