/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor042Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor042Cell039
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (627095/137438953472)
  b := (376257/68719476736)
  s := [(274877890431/274877906944),(-105681/4398046511104),(-5285/2199023255552)]
  L := [(10497939051833813183624394007/332306998946228968225951765070086144),(1864808427749/147573952589676412928),(279721170697/221360928884514619392),(-775/9223372036854775808),(-61/13835058055282163712)]
  c := (1165505364645/36893488147419103232)
  R := (-863519541905741/100000000000000)
  total := (-1948613761/250000000000000)
  k := 25
  n := 32
  sFloor := (1099511532661/2199023255552)
  nFloor := (900034858909/590295810358705651712)
  eFloor := (855756130655/590295810358705651712)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=627095,width:=125419,den:=137438953472,localDen:=996920996838686904677855295210258432,lowerC:=31493817155481216377967083520,s:=[996920936949710726788740609441005568,-23955091789255054839773134848,-2395939858748743195620802560],L:=[31493817155501439550873182021,12597525810491635369305440256,1259752160118648104877555712,-83766953069091225600,-4395513236313604096],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor042Source.source.poly i) 627095 125419 137438953472
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor042Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 10 21) (CoreQuotient.fused G u 10 21) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 10 21 WideAnchor042Source.data
    WideAnchor042Source.path_checked WideAnchor042Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor042Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 21 10) (CoreQuotient.fused G u 21 10) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 21 10 WideAnchor042Source.data
    WideAnchor042Source.path_swapped WideAnchor042Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor042Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor042Cell039
