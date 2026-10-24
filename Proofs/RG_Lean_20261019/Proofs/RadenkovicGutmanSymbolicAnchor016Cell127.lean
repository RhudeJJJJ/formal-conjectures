/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanSymbolicAnchor016Source
namespace Gebendorfer.RadenkovicGutman.SymbolicAnchor016Cell127
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (90327/134217728)
  b := (1589755/2147483648)
  s := [(4290723268443/4398046511104),(-10338852727/2199023255552),(-107484401/549755813888)]
  L := [(88113686902369120225389/4835703278458516698824704),(3000027736297/844424930131968),(22503047843/140737488355328),(-87964645/52776558133248),(-237843/8796093022208)]
  c := (641111451131/35184372088832)
  R := (-50064424696563/25000000000000)
  total := (-131600355753/1000000000000000)
  k := 6
  n := 32
  sFloor := (1067296421945/2199023255552)
  nFloor := (885836353795/18014398509481984)
  eFloor := (600489289851/18014398509481984)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1445232,width:=144523,den:=2147483648,localDen:=14507109835375550096474112,lowerC:=264341060707079732330496,s:=[14153100375666365829218304,-68206132747200639270912,-2836328368896919732224],L:=[264341060707107360676167,51540084057954108571648,2319596509104200220672,-24179537502671994880,-392266716127690752],transformed:=fun i => IntegerPolynomialPaymentCell.affine (SymbolicAnchor016Source.source.poly i) 1445232 144523 2147483648
}
theorem checked : IntegerPolynomialPaymentCell.checks SymbolicAnchor016Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 25) (CoreQuotient.fused G u 9 25) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 25 SymbolicAnchor016Source.data
    SymbolicAnchor016Source.path_checked SymbolicAnchor016Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry SymbolicAnchor016Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 25 9) (CoreQuotient.fused G u 25 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 25 9 SymbolicAnchor016Source.data
    SymbolicAnchor016Source.path_swapped SymbolicAnchor016Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry SymbolicAnchor016Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.SymbolicAnchor016Cell127
