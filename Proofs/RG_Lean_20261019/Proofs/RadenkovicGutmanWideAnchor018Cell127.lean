/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor018Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor018Cell127
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1388707/32768)
  b := (104153/2048)
  s := [(1889047091171/288230376151711744),(-4327147395673/1152921504606846976),(573392400737/576460752303423488)]
  L := [(1181888095647233829697/1180591620717411303424),(-359237201/824633720832),(141438433/1099511627776),(-12962879/412316860416),(335413/68719476736)]
  c := (550176159287/549755813888)
  R := (382155833/1000000000000)
  total := (388162779401/100000000000000)
  k := 0
  n := 32
  sFloor := (1093956442621/576460752303423488)
  nFloor := 31132067384868909866609971372059569569656500176808724590621767421006787915390988707462699183937102638486805604676156268148170948608
  eFloor := 31097509233642573568814183600259682802045191098903742627106223924774861973283151721181185765756353942788977425797499277588134100992
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1388707,width:=277741,den:=32768,localDen:=3541774862152233910272,lowerC:=3544482916764827516928,s:=[23212610656309248,-13292996799507456,3522922910128128],L:=[3545664286941701489091,-1542912029801578496,455605083099365376,-111350282734010368,17287054387838976],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor018Source.source.poly i) 1388707 277741 32768
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor018Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 27) (CoreQuotient.fused G u 9 27) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 27 WideAnchor018Source.data
    WideAnchor018Source.path_checked WideAnchor018Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor018Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 27 9) (CoreQuotient.fused G u 27 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 27 9 WideAnchor018Source.data
    WideAnchor018Source.path_swapped WideAnchor018Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor018Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor018Cell127
