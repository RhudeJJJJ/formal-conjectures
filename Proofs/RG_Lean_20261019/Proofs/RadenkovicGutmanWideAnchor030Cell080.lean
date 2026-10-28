/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor030Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor030Cell080
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1080087/134217728)
  b := (162013/16777216)
  s := [(2630680820919/8796093022208),(-395152569915/8796093022208),(7751422217/1099511627776)]
  L := [(117216254145173016375/147573952589676412928),(1026574518191/13194139533312),(-28930116571/2199023255552),(337060621/206158430208),(-20364975/137438953472)]
  c := (436664574389/549755813888)
  R := (-2878860860643/25000000000000)
  total := (-9434284089/62500000000000)
  k := 1
  n := 32
  sFloor := (574384907185/4398046511104)
  nFloor := (1397348548085/140737488355328)
  eFloor := (949216064081/140737488355328)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1080087,width:=216017,den:=134217728,localDen:=442721857769029238784,lowerC:=351648762435471409152,s:=[132406501078846144512,-19888680055257169920,3121134836203388928],L:=[351648762435519049125,34446124863572672512,-5824401775402156032,723832171982225408,-65600176206643200],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor030Source.source.poly i) 1080087 216017 134217728
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor030Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 39) (CoreQuotient.fused G u 9 39) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 39 WideAnchor030Source.data
    WideAnchor030Source.path_checked WideAnchor030Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor030Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 39 9) (CoreQuotient.fused G u 39 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 39 9 WideAnchor030Source.data
    WideAnchor030Source.path_swapped WideAnchor030Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor030Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor030Cell080
