/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor521Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor521Cell040
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (376257/68719476736)
  b := (112877/17179869184)
  s := [(4398046506785/4398046511104),(-27/68719476736),(-43/1099511627776)]
  L := [(1413333071835/2361183241434822606848),(35333138957/147573952589676412928),(7066590209/295147905179352825856),(-1/73786976294838206464)]
  c := (1413333071835/2361183241434822606848)
  R := (-66363993463357/6250000000000)
  total := (-11524821067/1000000000000000)
  k := 31
  n := 32
  sFloor := (1099511626221/2199023255552)
  nFloor := (581863172477/590295810358705651712)
  eFloor := (954475891465/1180591620717411303424)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=376257,width:=75251,den:=68719476736,localDen:=2361183241434822606848,lowerC:=1413333071835,s:=[2361183239116077137920,-927712935936,-92341796864],L:=[1413333071835,565330223312,56532721672,-32],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor521Source.source.poly i) 376257 75251 68719476736
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor521Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 6) (CoreQuotient.fused G u 4 6) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 4 6 WideAnchor521Source.data
    WideAnchor521Source.path_checked WideAnchor521Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor521Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 6 4) (CoreQuotient.fused G u 6 4) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 6 4 WideAnchor521Source.data
    WideAnchor521Source.path_swapped WideAnchor521Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor521Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor521Cell040
