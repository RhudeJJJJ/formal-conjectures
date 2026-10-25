/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor502Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor502Cell127
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1388707/32768)
  b := (104153/2048)
  s := [(7556188364685/1152921504606846976),(-1081786848919/288230376151711744),(286696200369/288230376151711744)]
  L := [(590944047823616914875/590295810358705651712),(-359237201/824633720832),(141438433/1099511627776),(-12962879/412316860416),(335413/68719476736)]
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
 left:=1388707,width:=277741,den:=32768,localDen:=1770887431076116955136,lowerC:=1772241458382413758464,s:=[11606305328156160,-6646498399758336,1761461455067136],L:=[1772832143470850744625,-771456014900789248,227802541549682688,-55675141367005184,8643527193919488],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor502Source.source.poly i) 1388707 277741 32768
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor502Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 32) (CoreQuotient.fused G u 4 32) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 4 32 WideAnchor502Source.data
    WideAnchor502Source.path_checked WideAnchor502Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor502Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 32 4) (CoreQuotient.fused G u 32 4) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 32 4 WideAnchor502Source.data
    WideAnchor502Source.path_swapped WideAnchor502Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor502Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor502Cell127
