/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor528Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor528Cell081
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (162013/16777216)
  b := (388831/33554432)
  s := [(4381456393335/4398046511104),(-3301722005/2199023255552),(-160608235/1099511627776)]
  L := [(163916713797120381683833/77371252455336267181195264),(1903333925493/2251799813685248),(94189282225/1125899906842624),(-24279341/140737488355328),(-580625/70368744177664)]
  c := (298162765461/140737488355328)
  R := (-38481325744703/12500000000000)
  total := (-2882567112403/500000000000000)
  k := 9
  n := 32
  sFloor := (136694078637/274877906944)
  nFloor := (227732820909/70368744177664)
  eFloor := (1624993182189/562949953421312)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=324026,width:=64805,den:=33554432,localDen:=77371252455336267181195264,lowerC:=163916713797108910522368,s:=[77079396017045247476367360,-116169015557804429148160,-11301799801541141463040],L:=[163916713797120381683833,65398055706877885415424,6472638188641425817600,-13347708872119287808,-638403938877440000],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor528Source.source.poly i) 324026 64805 33554432
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor528Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 8) (CoreQuotient.fused G u 4 8) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 4 8 WideAnchor528Source.data
    WideAnchor528Source.path_checked WideAnchor528Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor528Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 8 4) (CoreQuotient.fused G u 8 4) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 8 4 WideAnchor528Source.data
    WideAnchor528Source.path_swapped WideAnchor528Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor528Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor528Cell081
