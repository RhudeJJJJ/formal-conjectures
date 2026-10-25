/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor283Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor283Cell067
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (201899/268435456)
  b := (969115/1073741824)
  s := [(4397964545059/4398046511104),(-16392689/2199023255552),(-819495/1099511627776)]
  L := [(5658204626057/576460752303423488),(6789724238897/1729382256910270464),(113154403727/288230376151711744),(-564473/108086391056891904),(-4703/18014398509481984)]
  c := (707275578257/72057594037927936)
  R := (-288288897477249/50000000000000)
  total := (-170645008977/200000000000000)
  k := 17
  n := 32
  sFloor := (1099482120425/2199023255552)
  nFloor := (1886512351237/144115188075855872)
  eFloor := (1791013909407/144115188075855872)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=807596,width:=161519,den:=1073741824,localDen:=1729382256910270464,lowerC:=16974613878168,s:=[1729350026549919744,-12891735195648,-1288954183680],L:=[16974613878171,6789724238897,678926422362,-9031568,-451488],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor283Source.source.poly i) 807596 161519 1073741824
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor283Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 8) (CoreQuotient.fused G u 0 8) (((19/10) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (19/10) 0 8 WideAnchor283Source.data
    WideAnchor283Source.path_checked WideAnchor283Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor283Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 8 0) (CoreQuotient.fused G u 8 0) (((19/10) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (19/10) 8 0 WideAnchor283Source.data
    WideAnchor283Source.path_swapped WideAnchor283Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor283Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor283Cell067
