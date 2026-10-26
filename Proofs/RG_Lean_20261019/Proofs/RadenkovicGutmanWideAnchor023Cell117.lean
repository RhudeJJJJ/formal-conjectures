/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor023Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor023Cell117
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (897139/131072)
  b := (538283/65536)
  s := [(6462779429359/4503599627370496),(-3527817521055/4503599627370496),(449035534929/2251799813685248)]
  L := [(152977261424155043307/147573952589676412928),(-28482678423/2199023255552),(10884738217/3298534883328),(-93807929/137438953472),(18939575/206158430208)]
  c := (141063358779/137438953472)
  R := (260292987203/20000000000000)
  total := (20950124158411/1000000000000000)
  k := 0
  n := 32
  sFloor := (1916516489081/4503599627370496)
  nFloor := 19510102130278282674538438043764956194833267363739945877648743431200147767296
  eFloor := 18767045183957120257000034332457431237188280140405641796898969043476835991552
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=897139,width:=179427,den:=131072,localDen:=442721857769029238784,lowerC:=454396884464789618688,s:=[635317069023707136,-346798573589790720,88283978451320832],L:=[458931784272465129921,-5734320577934524416,1460924833360510976,-302176490370367488,40672427612569600],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor023Source.source.poly i) 897139 179427 131072
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor023Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 32) (CoreQuotient.fused G u 9 32) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 32 WideAnchor023Source.data
    WideAnchor023Source.path_checked WideAnchor023Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor023Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 32 9) (CoreQuotient.fused G u 32 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 32 9 WideAnchor023Source.data
    WideAnchor023Source.path_swapped WideAnchor023Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor023Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor023Cell117
