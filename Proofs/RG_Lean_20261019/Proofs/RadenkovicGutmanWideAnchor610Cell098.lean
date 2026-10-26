/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor610Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor610Cell098
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (224651/1048576)
  b := (269581/1048576)
  s := [(3577519564347/8796093022208),(-1169564922033/17592186044416),(81538763801/8796093022208)]
  L := [(4123523623105167983/9223372036854775808),(2921173852127/26388279066624),(-111426780163/13194139533312),(-321996013/824633720832),(162222757/824633720832)]
  c := (122890580389/274877906944)
  R := (-40251632760637/100000000000000)
  total := (-3726843764181/250000000000000)
  k := 2
  n := 32
  sFloor := (1537137933565/8796093022208)
  nFloor := (173934031245/17179869184)
  eFloor := (656327965953/68719476736)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=224651,width:=44930,den:=1048576,localDen:=27670116110564327424,lowerC:=12370570869309702144,s:=[11253903464114159616,-1839566561528512512,256498772374192128],L:=[12370570869315503949,3063072793167921152,-233678894872395776,-10804393322479616,5443292468609024],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor610Source.source.poly i) 224651 44930 1048576
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor610Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 6 8) (CoreQuotient.fused G u 6 8) (((21/11) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (21/11) 6 8 WideAnchor610Source.data
    WideAnchor610Source.path_checked WideAnchor610Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor610Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 8 6) (CoreQuotient.fused G u 8 6) (((21/11) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (21/11) 8 6 WideAnchor610Source.data
    WideAnchor610Source.path_swapped WideAnchor610Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor610Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor610Cell098
