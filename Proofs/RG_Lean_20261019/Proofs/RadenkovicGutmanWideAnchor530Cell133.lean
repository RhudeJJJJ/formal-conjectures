/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor530Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor530Cell133
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (518331/4096)
  b := 128
  s := [(568778031947/2305843009213693952),(-78410554831/9223372036854775808),(437883429/2305843009213693952)]
  L := [(77380874930699209221241647/77371252455336267181195264),(-12544273/4398046511104),(323521/6597069766656),(-199/274877906944),(-1/412316860416)]
  c := (274911322107/274877906944)
  R := (379863333/6250000000000)
  total := (44702975277/500000000000000)
  k := 0
  n := 32
  sFloor := (2198453106673/18446744073709551616)
  nFloor := 37480772557320508753735882836123883211262038198569448371816687992832
  eFloor := 37476093255689489916779358611375096768019262911239029199710975950848
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=518331,width:=5957,den:=4096,localDen:=232113757366008801543585792,lowerC:=232141973962690424865816576,s:=[57255071388178317312,-1973266222619295744,44078789226921984],L:=[232142624792097627663724941,-662043553223833288704,11382883242551017472,-168040561096261632,-562949953421312],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor530Source.source.poly i) 518331 5957 4096
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor530Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 8) (CoreQuotient.fused G u 4 8) (((32/17) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (32/17) 4 8 WideAnchor530Source.data
    WideAnchor530Source.path_checked WideAnchor530Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor530Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 8 4) (CoreQuotient.fused G u 8 4) (((32/17) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (32/17) 8 4 WideAnchor530Source.data
    WideAnchor530Source.path_swapped WideAnchor530Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor530Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor530Cell133
