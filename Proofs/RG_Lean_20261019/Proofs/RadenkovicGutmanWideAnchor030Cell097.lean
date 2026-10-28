/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor030Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor030Cell097
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (748837/4194304)
  b := (224651/1048576)
  s := [(4886460806685/17592186044416),(2646030199/4398046511104),(-12441478519/4398046511104)]
  L := [(50386455677124705323/73786976294838206464),(210311873021/26388279066624),(31629597835/4398046511104),(-2234663663/1649267441664),(42494657/274877906944)]
  c := (750816698031/1099511627776)
  R := (-9536496016701/50000000000000)
  total := (-3326318668589/500000000000000)
  k := 1
  n := 32
  sFloor := (1211819753351/8796093022208)
  nFloor := (1205130514339/536870912)
  eFloor := (249384370325/134217728)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=748837,width:=149767,den:=4194304,localDen:=221360928884514619392,lowerC:=151159367031274340352,s:=[61485906321966366720,133179060573437952,-626200117417869312],L:=[151159367031374115969,1764223860518944768,1591969784612782080,-299931479692017664,34221217888075776],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor030Source.source.poly i) 748837 149767 4194304
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor030Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 39) (CoreQuotient.fused G u 9 39) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 39 WideAnchor030Source.data
    WideAnchor030Source.path_checked WideAnchor030Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor030Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 39 9) (CoreQuotient.fused G u 39 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 39 9 WideAnchor030Source.data
    WideAnchor030Source.path_swapped WideAnchor030Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor030Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor030Cell097
