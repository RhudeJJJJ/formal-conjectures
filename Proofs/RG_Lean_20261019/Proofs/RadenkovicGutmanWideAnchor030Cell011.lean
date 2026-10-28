/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor030Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor030Cell011
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (60867/2199023255552)
  b := (584323/17592186044416)
  s := [(4398046510789/4398046511104),(-63/2199023255552),(-3/1099511627776)]
  L := [(562672166977406547867367649/10633823966279326983230456482242756608),(599702699663/28334198897217871282176),(29985073385/14167099448608935641088),(7/7083549724304467820544),(-1/1770887431076116955136)]
  c := (499753276075/9444732965739290427392)
  R := (-1183118190757143/100000000000000)
  total := (-16244073/250000000000000)
  k := 35
  n := 32
  sFloor := (2199023255325/4398046511104)
  nFloor := (554507465393/4835703278458516698824704)
  eFloor := (374722934875/4835703278458516698824704)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=486936,width:=97387,den:=17592186044416,localDen:=31901471898837980949691369446728269824,lowerC:=1688016500931415960348262400,s:=[31901471896553111150619720306533597184,-913947919628659656077869056,-87042659012253300578844672],L:=[1688016500932219643602102947,675205213683841819278835712,67520382661681488571924480,31525197391593472,-18014398509481984],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor030Source.source.poly i) 486936 97387 17592186044416
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor030Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 39) (CoreQuotient.fused G u 9 39) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 39 WideAnchor030Source.data
    WideAnchor030Source.path_checked WideAnchor030Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor030Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 39 9) (CoreQuotient.fused G u 39 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 39 9 WideAnchor030Source.data
    WideAnchor030Source.path_swapped WideAnchor030Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor030Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor030Cell011
