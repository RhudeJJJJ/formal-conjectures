/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor521Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor521Cell018
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (872389/8796093022208)
  b := (523433/4398046511104)
  s := [(2199023255551/2199023255552),(1/4398046511104),(-1/2199023255552)]
  L := [(3798968662539/19342813113834066795298816),(284921343287/3626777458843887524118528),(113968014779/14507109835375550096474112),(-1/453347182355485940514816),(1/906694364710971881029632)]
  c := (1899484331269/9671406556917033397649408)
  R := (-731465310645167/50000000000000)
  total := (-288323847/1000000000000000)
  k := 43
  n := 32
  sFloor := (1099511627775/2199023255552)
  nFloor := (782009562441/2417851639229258349412352)
  eFloor := (1282791744921/4835703278458516698824704)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=872389,width:=174477,den:=8796093022208,localDen:=58028439341502200385896448,lowerC:=11396905987614,s:=[58028439341475812106829824,13194139533312,-26388279066624],L:=[11396905987617,4558741492592,455872059116,-128,64],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor521Source.source.poly i) 872389 174477 8796093022208
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor521Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 6) (CoreQuotient.fused G u 4 6) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 4 6 WideAnchor521Source.data
    WideAnchor521Source.path_checked WideAnchor521Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor521Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 6 4) (CoreQuotient.fused G u 6 4) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 6 4 WideAnchor521Source.data
    WideAnchor521Source.path_swapped WideAnchor521Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor521Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor521Cell018
