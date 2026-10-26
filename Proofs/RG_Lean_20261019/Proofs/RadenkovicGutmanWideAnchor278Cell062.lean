/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor278Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor278Cell062
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1298221/4294967296)
  b := (1557865/4294967296)
  s := [(4398038115155/4398046511104),(-3358369/4398046511104),(-167915/2199023255552)]
  L := [(492900613338959249004288991/324518553658426726783156020576256),(4202712947779/6917529027641081856),(70044680625/1152921504606846976),(-36085/432345564227567616),(-301/72057594037927936)]
  c := (875567375649/576460752303423488)
  R := (-669877285527953/100000000000000)
  total := (-399295048077/1000000000000000)
  k := 20
  n := 32
  sFloor := (1099508605239/2199023255552)
  nFloor := (806841172391/288230376151711744)
  eFloor := (126761857699/72057594037927936)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1298221,width:=259644,den:=4294967296,localDen:=973555660975280180349468061728768,lowerC:=1478701840016474809999294464,s:=[973553802440210673337833892085760,-743411681376958477812891648,-74339640747286544630415360],L:=[1478701840016877747012866973,591479264548833225460416512,59147474542881637662720000,-81256196276832174080,-4066750463515557888],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor278Source.source.poly i) 1298221 259644 4294967296
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor278Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 6) (CoreQuotient.fused G u 0 6) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 6 WideAnchor278Source.data
    WideAnchor278Source.path_checked WideAnchor278Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor278Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 6 0) (CoreQuotient.fused G u 6 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 6 0 WideAnchor278Source.data
    WideAnchor278Source.path_swapped WideAnchor278Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor278Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor278Cell062
