/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor037Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor037Cell044
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (780205/68719476736)
  b := (468123/34359738368)
  s := [(4398046445387/4398046511104),(-1643/274877906944),(-657/1099511627776)]
  L := [(5565869362485/1180591620717411303424),(417440201707/221360928884514619392),(166976079907/885443715538058477568),(-17/110680464442257309696),(-1/55340232221128654848)]
  c := (1391467340621/295147905179352825856)
  R := (-479315708276687/50000000000000)
  total := (-10777380827/500000000000000)
  k := 28
  n := 32
  sFloor := (2199023208235/4398046511104)
  nFloor := (1391723412795/295147905179352825856)
  eFloor := (551373246049/73786976294838206464)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=780205,width:=156041,den:=68719476736,localDen:=3541774862152233910272,lowerC:=16697608087452,s:=[3541774809229915324416,-21169893801984,-2116345135104],L:=[16697608087455,6679043227312,667904319628,-544,-64],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor037Source.source.poly i) 780205 156041 68719476736
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor037Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 10 16) (CoreQuotient.fused G u 10 16) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 10 16 WideAnchor037Source.data
    WideAnchor037Source.path_checked WideAnchor037Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor037Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 16 10) (CoreQuotient.fused G u 16 10) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 16 10 WideAnchor037Source.data
    WideAnchor037Source.path_swapped WideAnchor037Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor037Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor037Cell044
