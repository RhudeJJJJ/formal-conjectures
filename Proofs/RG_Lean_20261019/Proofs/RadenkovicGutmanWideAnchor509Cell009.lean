/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor509Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor509Cell009
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1352601/70368744177664)
  b := (1623121/70368744177664)
  s := [(2199023255551/2199023255552),(-3/4398046511104),(1/2199023255552)]
  L := [(4024170817755/19342813113834066795298816),(4829001411125/58028439341502200385896448),(241449892079/29014219670751100192948224),(-5/3626777458843887524118528),(1/1813388729421943762059264)]
  c := (2012085408877/9671406556917033397649408)
  R := (-1460051158473517/100000000000000)
  total := (-13942177/250000000000000)
  k := 43
  n := 32
  sFloor := (1099511627775/2199023255552)
  nFloor := (699499737531/19342813113834066795298816)
  eFloor := (332961127133/9671406556917033397649408)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1352601,width:=270520,den:=70368744177664,localDen:=58028439341502200385896448,lowerC:=12072512453262,s:=[58028439341475812106829824,-39582418599936,26388279066624],L:=[12072512453265,4829001411125,482899784158,-80,32],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor509Source.source.poly i) 1352601 270520 70368744177664
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor509Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 39) (CoreQuotient.fused G u 4 39) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 4 39 WideAnchor509Source.data
    WideAnchor509Source.path_checked WideAnchor509Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor509Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 39 4) (CoreQuotient.fused G u 39 4) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 39 4 WideAnchor509Source.data
    WideAnchor509Source.path_swapped WideAnchor509Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor509Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor509Cell009
