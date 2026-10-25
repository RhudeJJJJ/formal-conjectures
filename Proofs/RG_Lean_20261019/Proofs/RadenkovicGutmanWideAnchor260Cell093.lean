/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor260Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor260Cell093
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (722259/8388608)
  b := (433355/4194304)
  s := [(5239610457057/8796093022208),(-159058791979/8796093022208),(253198973/4398046511104)]
  L := [(91855074632353855493/295147905179352825856),(1415192596571/52776558133248),(17649755723/26388279066624),(231446995/3298534883328),(-62665055/1649267441664)]
  c := (1368747273569/4398046511104)
  R := (-58363227246077/100000000000000)
  total := (-4841668766139/500000000000000)
  k := 2
  n := 32
  sFloor := (317566128939/1099511627776)
  nFloor := (973453372889/274877906944)
  eFloor := (1585141879841/549755813888)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=722259,width:=144451,den:=8388608,localDen:=885443715538058477568,lowerC:=275565223896938446848,s:=[527436458363424079872,-16011382258384502784,50975686331990016],L:=[275565223897061566479,23742991874272526336,592227528224014336,62128579642654720,-33643045228380160],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor260Source.source.poly i) 722259 144451 8388608
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor260Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 37) (CoreQuotient.fused G u 0 37) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 37 WideAnchor260Source.data
    WideAnchor260Source.path_checked WideAnchor260Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor260Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 37 0) (CoreQuotient.fused G u 37 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 37 0 WideAnchor260Source.data
    WideAnchor260Source.path_swapped WideAnchor260Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor260Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor260Cell093
