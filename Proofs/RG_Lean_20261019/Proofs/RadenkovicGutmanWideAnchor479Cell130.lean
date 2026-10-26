/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor479Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor479Cell130
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1199841/16384)
  b := (1439809/16384)
  s := [(183328220039/144115188075855872),(-3362532459835/4611686018427387904),(445903911735/2305843009213693952)]
  L := [(4724114273155891780849/4722366482869645213696),(-648226631/4398046511104),(288345577/6597069766656),(-2948401/274877906944),(688655/412316860416)]
  c := (1099794610661/1099511627776)
  R := (3216729003/25000000000000)
  total := (112993186583/50000000000000)
  k := 0
  n := 32
  sFloor := (1697889202441/4611686018427387904)
  nFloor := 27119166676107352115369473742274052226854186694594608808327118848000
  eFloor := 27109064330274557650009142657130535712972489603783634361301870837760
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1199841,width:=239968,den:=16384,localDen:=14167099448608935641088,lowerC:=14170745655318143827968,s:=[18021897342713856,-10329699716613120,2739633633699840],L:=[14172342819467675342547,-2088084135405944832,619217411580624896,-151959430445924352,23662005625815040],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor479Source.source.poly i) 1199841 239968 16384
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor479Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 10) (CoreQuotient.fused G u 4 10) (((21/11) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (21/11) 4 10 WideAnchor479Source.data
    WideAnchor479Source.path_checked WideAnchor479Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor479Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 10 4) (CoreQuotient.fused G u 10 4) (((21/11) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (21/11) 10 4 WideAnchor479Source.data
    WideAnchor479Source.path_swapped WideAnchor479Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor479Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor479Cell130
