/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor010Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor010Cell023
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1085389/4398046511104)
  b := (651233/2199023255552)
  s := [(274877906055/274877906944),(-2845/2199023255552),(-71/549755813888)]
  L := [(2764873920485/1180591620717411303424),(1658918233111/1770887431076116955136),(6912133741/73786976294838206464),(-31/110680464442257309696)]
  c := (691218480121/295147905179352825856)
  R := (-248403581096391/25000000000000)
  total := (-97159549/200000000000000)
  k := 29
  n := 32
  sFloor := (2199023245311/4398046511104)
  nFloor := (824669176095/151115727451828646838272)
  eFloor := (1138811943803/302231454903657293676544)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1085389,width:=217077,den:=4398046511104,localDen:=3541774862152233910272,lowerC:=8294621761452,s:=[3541774850697556131840,-4582193233920,-457414017024],L:=[8294621761455,3317836466222,331782419568,-992],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor010Source.source.poly i) 1085389 217077 4398046511104
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor010Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 19) (CoreQuotient.fused G u 9 19) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 19 WideAnchor010Source.data
    WideAnchor010Source.path_checked WideAnchor010Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor010Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 19 9) (CoreQuotient.fused G u 19 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 19 9 WideAnchor010Source.data
    WideAnchor010Source.path_swapped WideAnchor010Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor010Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor010Cell023
