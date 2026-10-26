/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor025Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor025Cell084
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (139979/8388608)
  b := (671899/33554432)
  s := [(5423577016053/17592186044416),(-674324247239/17592186044416),(59293787499/8796093022208)]
  L := [(171039139449162329963/295147905179352825856),(453815191981/8796093022208),(-40810110687/4398046511104),(689587659/549755813888),(-33022337/274877906944)]
  c := (637170446847/1099511627776)
  R := (-5455841882039/20000000000000)
  total := (-84583686833/100000000000000)
  k := 1
  n := 32
  sFloor := (1216960085953/8796093022208)
  nFloor := (552641301215/17592186044416)
  eFloor := (252100132317/8796093022208)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=559916,width:=111983,den:=33554432,localDen:=295147905179352825856,lowerC:=171039139449098207232,s:=[90992523090956648448,-11313283549966106624,1989569360657645568],L:=[171039139449162329963,15227510999893409792,-2738720167918829568,370219555391275008,-35457464363122688],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor025Source.source.poly i) 559916 111983 33554432
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor025Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 34) (CoreQuotient.fused G u 9 34) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 34 WideAnchor025Source.data
    WideAnchor025Source.path_checked WideAnchor025Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor025Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 34 9) (CoreQuotient.fused G u 34 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 34 9 WideAnchor025Source.data
    WideAnchor025Source.path_swapped WideAnchor025Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor025Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor025Cell084
