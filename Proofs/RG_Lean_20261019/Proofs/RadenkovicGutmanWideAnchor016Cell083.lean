/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor016Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor016Cell083
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (466597/33554432)
  b := (139979/8388608)
  s := [(8468617284575/35184372088832),(-1149017114389/35184372088832),(101737493591/17592186044416)]
  L := [(132055325961570739489/147573952589676412928),(395447350051/6597069766656),(-7124515327/549755813888),(378293623/206158430208),(-1651053/8589934592)]
  c := (1967777698659/2199023255552)
  R := (-5555422638893/100000000000000)
  total := (-896315591/7812500000000)
  k := 1
  n := 32
  sFloor := (940384394671/8796093022208)
  nFloor := (767057050989/35184372088832)
  eFloor := (524607956631/35184372088832)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=466597,width:=93319,den:=33554432,localDen:=442721857769029238784,lowerC:=396165977884619440128,s:=[106559866053486182400,-14457981236850720768,2560307857912233984],L:=[396165977884712218467,26538022433732952064,-5737417561746702336,812379369535176704,-85094623667552256],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor016Source.source.poly i) 466597 93319 33554432
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor016Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 25) (CoreQuotient.fused G u 9 25) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 25 WideAnchor016Source.data
    WideAnchor016Source.path_checked WideAnchor016Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor016Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 25 9) (CoreQuotient.fused G u 25 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 25 9 WideAnchor016Source.data
    WideAnchor016Source.path_swapped WideAnchor016Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor016Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor016Cell083
