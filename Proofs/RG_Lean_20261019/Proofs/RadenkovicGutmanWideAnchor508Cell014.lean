/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor508Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor508Cell014
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (841425/17592186044416)
  b := (504855/8796093022208)
  s := [(4398046511095/4398046511104),(-1/1099511627776)]
  L := [(949801542149382609421224499/1361129467683753853853498429727072845824),(2024623758563/7253554917687775048237056),(101231187907/3626777458843887524118528),(1/113336795588871485128704),(-1/226673591177742970257408)]
  c := (1687186465469/2417851639229258349412352)
  R := (-279908381811657/20000000000000)
  total := (-16622759/125000000000000)
  k := 41
  n := 32
  sFloor := (2199023255545/4398046511104)
  nFloor := (702366590257/4835703278458516698824704)
  eFloor := (246974778241/1208925819614629174706176)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=841425,width:=168285,den:=17592186044416,localDen:=4083388403051261561560495289181218537472,lowerC:=2849404626446524731290025984,s:=[4083388403042905466295318972325649448960,-3713820117856140824697372672],L:=[2849404626448147828263673497,1139761850578722482506694656,113976185034059465220947968,36028797018963968,-18014398509481984],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor508Source.source.poly i) 841425 168285 17592186044416
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor508Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 38) (CoreQuotient.fused G u 4 38) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 4 38 WideAnchor508Source.data
    WideAnchor508Source.path_checked WideAnchor508Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor508Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 38 4) (CoreQuotient.fused G u 38 4) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 38 4 WideAnchor508Source.data
    WideAnchor508Source.path_swapped WideAnchor508Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor508Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor508Cell014
