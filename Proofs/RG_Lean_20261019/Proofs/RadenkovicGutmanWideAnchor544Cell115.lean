/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor544Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor544Cell115
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1246027/262144)
  b := (23363/4096)
  s := [(4447476270485/1125899906842624),(-2316067293619/1125899906842624),(283282529947/562949953421312)]
  L := [(2520988840176286052507/2361183241434822606848),(-94227292951/4398046511104),(30513531629/6597069766656),(-207976217/274877906944),(32022499/412316860416)]
  c := (577354581217/549755813888)
  R := (2449119918961/100000000000000)
  total := (26944320374173/1000000000000000)
  k := 0
  n := 32
  sFloor := (337246754595/281474976710656)
  nFloor := 24535442876091542999432420906331259359199232
  eFloor := 22799304036152082670187741417229509216698368
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1246027,width:=249205,den:=262144,localDen:=7083549724304467820544,lowerC:=7439157133568372637696,s:=[27981101266800476160,-14571435470843019264,3564519145460465664],L:=[7562966520528858157521,-151763678105683623936,32763655108004151296,-5359506302164795392,550142343764770816],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor544Source.source.poly i) 1246027 249205 262144
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor544Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 5 22) (CoreQuotient.fused G u 5 22) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 5 22 WideAnchor544Source.data
    WideAnchor544Source.path_checked WideAnchor544Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor544Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 22 5) (CoreQuotient.fused G u 22 5) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 22 5 WideAnchor544Source.data
    WideAnchor544Source.path_swapped WideAnchor544Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor544Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor544Cell115
