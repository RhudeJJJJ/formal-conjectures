/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor606Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor606Cell013
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1402375/35184372088832)
  b := (841425/17592186044416)
  s := [(4398046511103/4398046511104)]
  L := [(398054462294705685504607511/21778071482940061661655974875633165533184),(3394016479471/464227514732017603087171584),(169700823937/232113757366008801543585792),(5/29014219670751100192948224),(-1/14507109835375550096474112)]
  c := (1414173533101/77371252455336267181195264)
  R := (-49426704886433/3125000000000)
  total := (-125335647/1000000000000000)
  k := 46
  n := 32
  sFloor := (2199023255551/4398046511104)
  nFloor := (553335325429/19342813113834066795298816)
  eFloor := (913350582607/19342813113834066795298816)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1402375,width:=280475,den:=35184372088832,localDen:=65334214448820184984967924626899496599552,lowerC:=1194163386883290260746272768,s:=[65334214448805329704496500063600707108864],L:=[1194163386884117056513822533,477665354757341196465471488,47766535465446209247772672,11258999068426240,-4503599627370496],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor606Source.source.poly i) 1402375 280475 35184372088832
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor606Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 6 6) (CoreQuotient.fused G u 6 6) (((44/23) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (44/23) 6 6 WideAnchor606Source.data
    WideAnchor606Source.path_checked WideAnchor606Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor606Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 6 6) (CoreQuotient.fused G u 6 6) (((44/23) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (44/23) 6 6 WideAnchor606Source.data
    WideAnchor606Source.path_swapped WideAnchor606Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor606Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor606Cell013
