/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor506Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor506Cell042
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1083619/137438953472)
  b := (650171/68719476736)
  s := [(4398046326497/4398046511104),(-36921/2199023255552),(-923/549755813888)]
  L := [(2495245420211571470432802227/166153499473114484112975882535043072),(166216107733/27670116110564327424),(132972351355/221360928884514619392),(-1111/27670116110564327424),(-25/13835058055282163712)]
  c := (1108111567043/73786976294838206464)
  R := (-900701776274741/100000000000000)
  total := (-7027534603/500000000000000)
  k := 26
  n := 32
  sFloor := (2199023122635/4398046511104)
  nFloor := (280183987673/73786976294838206464)
  eFloor := (48944732381/9223372036854775808)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1083619,width:=216723,den:=137438953472,localDen:=498460498419343452338927647605129216,lowerC:=7485736260629686794156244992,s:=[498460477496577629064129392450469888,-8369015659873448204873760768,-836878898628227046190350336],L:=[7485736260634714411298406681,2994283203397252074566582272,299427116006478334436311040,-20013996744034484224,-900719925474099200],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor506Source.source.poly i) 1083619 216723 137438953472
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor506Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 36) (CoreQuotient.fused G u 4 36) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 4 36 WideAnchor506Source.data
    WideAnchor506Source.path_checked WideAnchor506Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor506Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 36 4) (CoreQuotient.fused G u 36 4) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 36 4 WideAnchor506Source.data
    WideAnchor506Source.path_swapped WideAnchor506Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor506Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor506Cell042
