/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor005Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor005Cell012
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (584323/17592186044416)
  b := (1402375/35184372088832)
  s := [(4398046511039/4398046511104),(-3/549755813888),(-1/1099511627776)]
  L := [(10383700993685250113915073659/1361129467683753853853498429727072845824),(5533542748405/1813388729421943762059264),(276676900735/906694364710971881029632),(-19/113336795588871485128704),(5/56668397794435742564352)]
  c := (1152822392401/151115727451828646838272)
  R := (-1279954929865689/100000000000000)
  total := (-84404459/1000000000000000)
  k := 37
  n := 32
  sFloor := (2199023255505/4398046511104)
  nFloor := (300085476523/4835703278458516698824704)
  eFloor := (1148639204661/19342813113834066795298816)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1168646,width:=233729,den:=35184372088832,localDen:=4083388403051261561560495289181218537472,lowerC:=31151102981049043917132005376,s:=[4083388402990911984645333000779886231552,-22282920707136844948184236032,-3713820117856140824697372672],L:=[31151102981055750341745220977,12460430529877734149524029440,1246041987052169710859714560,-684547143360315392,360287970189639680],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor005Source.source.poly i) 1168646 233729 35184372088832
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor005Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 14) (CoreQuotient.fused G u 9 14) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 14 WideAnchor005Source.data
    WideAnchor005Source.path_checked WideAnchor005Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor005Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 14 9) (CoreQuotient.fused G u 14 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 14 9 WideAnchor005Source.data
    WideAnchor005Source.path_swapped WideAnchor005Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor005Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor005Cell012
