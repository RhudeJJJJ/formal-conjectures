/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor273Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor273Cell052
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (838683/17179869184)
  b := (1006419/17179869184)
  s := [(2199023177709/2199023255552),(-62271/4398046511104),(-3115/2199023255552)]
  L := [(4715508894397/147573952589676412928),(2829295129777/221360928884514619392),(141464233181/110680464442257309696),(-215/6917529027641081856),(-11/6917529027641081856)]
  c := (1178877223599/36893488147419103232)
  R := (-431474578509589/50000000000000)
  total := (-3333562387/40000000000000)
  k := 25
  n := 32
  sFloor := (1099511571729/2199023255552)
  nFloor := (1222314690191/18446744073709551616)
  eFloor := (338525715539/9223372036854775808)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=838683,width:=167736,den:=17179869184,localDen:=442721857769029238784,lowerC:=14146526683188,s:=[442721842097163337728,-6268404105216,-627132334080],L:=[14146526683191,5658590259554,565856932724,-13760,-704],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor273Source.source.poly i) 838683 167736 17179869184
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor273Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 4) (CoreQuotient.fused G u 0 4) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 4 WideAnchor273Source.data
    WideAnchor273Source.path_checked WideAnchor273Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor273Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 0) (CoreQuotient.fused G u 4 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 4 0 WideAnchor273Source.data
    WideAnchor273Source.path_swapped WideAnchor273Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor273Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor273Cell052
