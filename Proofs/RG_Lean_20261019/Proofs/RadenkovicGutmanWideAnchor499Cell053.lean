/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor499Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor499Cell053
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1006419/17179869184)
  b := (603851/8589934592)
  s := [(4398021927873/4398046511104),(-9833139/4398046511104),(-491623/2199023255552)]
  L := [(242934248203441166057013377/81129638414606681695789005144064),(4142708725201/3458764513820540928),(207126857695/1729382256910270464),(-193891/216172782113783808),(-4843/108086391056891904)]
  c := (863075826641/288230376151711744)
  R := (-635938404214819/100000000000000)
  total := (-18352430429/250000000000000)
  k := 19
  n := 32
  sFloor := (68718923617/137438953472)
  nFloor := (1247566415477/4611686018427387904)
  eFloor := (1164407031591/4611686018427387904)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1006419,width:=201283,den:=17179869184,localDen:=243388915243820045087367015432192,lowerC:=728802744609916950820159488,s:=[243387554802107759438564167778304,-544168195722636800003407872,-54413061970495865364676608],L:=[728802744610323498171040131,291517210486245720498110464,29150513722925742251048960,-218301858837623209984,-10905466497677656064],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor499Source.source.poly i) 1006419 201283 17179869184
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor499Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 29) (CoreQuotient.fused G u 4 29) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 4 29 WideAnchor499Source.data
    WideAnchor499Source.path_checked WideAnchor499Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor499Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 29 4) (CoreQuotient.fused G u 29 4) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 29 4 WideAnchor499Source.data
    WideAnchor499Source.path_swapped WideAnchor499Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor499Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor499Cell053
