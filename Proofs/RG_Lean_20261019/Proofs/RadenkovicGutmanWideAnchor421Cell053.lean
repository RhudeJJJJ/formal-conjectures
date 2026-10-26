/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor421Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor421Cell053
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1006419/17179869184)
  b := (603851/8589934592)
  s := [(4398046234189/4398046511104),(-55383/2199023255552),(-2769/1099511627776)]
  L := [(2072825600823/73786976294838206464),(2487380800663/221360928884514619392),(41456179633/36893488147419103232),(-175/13835058055282163712),(-1/2305843009213693952)]
  c := (2072825600823/73786976294838206464)
  R := (-869389004999873/100000000000000)
  total := (-25190319727/250000000000000)
  k := 26
  n := 32
  sFloor := (2199023056173/4398046511104)
  nFloor := (2025515056859/36893488147419103232)
  eFloor := (283738750015/4611686018427387904)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1006419,width:=201283,den:=17179869184,localDen:=221360928884514619392,lowerC:=6218476802469,s:=[221360914946926313472,-5575035322368,-557473333248],L:=[6218476802469,2487380800663,248737077798,-2800,-96],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor421Source.source.poly i) 1006419 201283 17179869184
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor421Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 4) (CoreQuotient.fused G u 2 4) (((15/8) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (15/8) 2 4 WideAnchor421Source.data
    WideAnchor421Source.path_checked WideAnchor421Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor421Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 2) (CoreQuotient.fused G u 4 2) (((15/8) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (15/8) 4 2 WideAnchor421Source.data
    WideAnchor421Source.path_swapped WideAnchor421Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor421Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor421Cell053
