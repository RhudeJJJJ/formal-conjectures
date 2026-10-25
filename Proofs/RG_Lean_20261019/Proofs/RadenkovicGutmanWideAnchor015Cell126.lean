/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor015Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor015Cell126
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (144657/4096)
  b := (1388707/32768)
  s := [(1630511207801/144115188075855872),(-1866350074561/288230376151711744),(247187375065/144115188075855872)]
  L := [(295613101958504184157/295147905179352825856),(-8232063463/13194139533312),(404165211/2199023255552),(-36953891/824633720832),(954489/137438953472)]
  c := (550359531099/549755813888)
  R := (54877633909/100000000000000)
  total := (2321652767941/500000000000000)
  k := 0
  n := 32
  sFloor := (1889047091171/576460752303423488)
  nFloor := 7537709464516860269507347465025621346248337244720273231672553835884301247336675537634748987812434423356377964478464
  eFloor := 7525677277791640643085307921231361106797785295987949323573186617066076414990414164608748304588635414977813367750656
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1157256,width:=231451,den:=32768,localDen:=885443715538058477568,lowerC:=886416070167037476864,s:=[10017860860729344,-5733427429051392,1518719232399360],L:=[886839305875512552471,-552444427377836032,162738409071181824,-39678938326237184,6149248559087616],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor015Source.source.poly i) 1157256 231451 32768
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor015Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 24) (CoreQuotient.fused G u 9 24) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 24 WideAnchor015Source.data
    WideAnchor015Source.path_checked WideAnchor015Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor015Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 24 9) (CoreQuotient.fused G u 24 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 24 9 WideAnchor015Source.data
    WideAnchor015Source.path_swapped WideAnchor015Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor015Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor015Cell126
