/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor017Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor017Cell124
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1607301/65536)
  b := (241095/8192)
  s := [(303231657309/9007199254740992),(-2770912140795/144115188075855872),(366348256823/72057594037927936)]
  L := [(592206812309571978273/590295810358705651712),(-5599732115/4398046511104),(2455832825/6597069766656),(-24761087/274877906944),(5723083/412316860416)]
  c := (550998367969/549755813888)
  R := (56441057833/50000000000000)
  total := (331264122501/50000000000000)
  k := 0
  n := 32
  sFloor := (1406745444897/144115188075855872)
  nFloor := 5589005911823715838468117884399696002368325253388379712298796954256355331285588560554579384787917898631872512
  eFloor := 5570595504839129063445819820519949145686730872178772841652994435317433424080320871472873442662314754604793856
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1607301,width:=321459,den:=65536,localDen:=1770887431076116955136,lowerC:=1774889977932171706368,s:=[59617769680207872,-34048968386088960,9003374759682048],L:=[1776620436928715934819,-2254749965651804160,659232604238643200,-159522088317616128,24580454317293568],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor017Source.source.poly i) 1607301 321459 65536
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor017Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 26) (CoreQuotient.fused G u 9 26) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 26 WideAnchor017Source.data
    WideAnchor017Source.path_checked WideAnchor017Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor017Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 26 9) (CoreQuotient.fused G u 26 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 26 9 WideAnchor017Source.data
    WideAnchor017Source.path_swapped WideAnchor017Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor017Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor017Cell124
