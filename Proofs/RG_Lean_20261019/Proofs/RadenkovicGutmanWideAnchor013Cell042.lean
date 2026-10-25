/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor013Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor013Cell042
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1083619/137438953472)
  b := (650171/68719476736)
  s := [(4398042245505/4398046511104),(-213279/549755813888),(-42655/1099511627776)]
  L := [(4709642580315/9223372036854775808),(5651544335689/27670116110564327424),(282574994099/13835058055282163712),(-29521/1729382256910270464),(-731/864691128455135232)]
  c := (588705322539/1152921504606846976)
  R := (-9054774524677/1250000000000)
  total := (-11274739761/1000000000000000)
  k := 21
  n := 32
  sFloor := (1099510092163/2199023255552)
  nFloor := (1345285389817/295147905179352825856)
  eFloor := (319408583067/73786976294838206464)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1083619,width:=216723,den:=137438953472,localDen:=27670116110564327424,lowerC:=14128927740936,s:=[27670089273735905280,-10734683553792,-1073448222720],L:=[14128927740945,5651544335689,565149988198,-472336,-23392],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor013Source.source.poly i) 1083619 216723 137438953472
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor013Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 22) (CoreQuotient.fused G u 9 22) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 22 WideAnchor013Source.data
    WideAnchor013Source.path_checked WideAnchor013Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor013Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 22 9) (CoreQuotient.fused G u 22 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 22 9 WideAnchor013Source.data
    WideAnchor013Source.path_swapped WideAnchor013Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor013Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor013Cell042
