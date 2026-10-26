/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor539Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor539Cell014
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (841425/17592186044416)
  b := (504855/8796093022208)
  s := [(4398046510175/4398046511104),(-371/4398046511104),(-19/2199023255552)]
  L := [(2597234423725/18889465931478580854784),(1558340653891/28334198897217871282176),(25972344213/4722366482869645213696),(-5/3541774862152233910272)]
  c := (649308605931/4722366482869645213696)
  R := (-45414846099551/4000000000000)
  total := (-4308471/40000000000000)
  k := 33
  n := 32
  sFloor := (2199023254883/4398046511104)
  nFloor := (180818686085/1208925819614629174706176)
  eFloor := (1110515853921/9671406556917033397649408)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=841425,width:=168285,den:=17592186044416,localDen:=56668397794435742564352,lowerC:=7791703271172,s:=[56668397782465668710400,-4780298600448,-489626271744],L:=[7791703271175,3116681307782,311668130556,-80],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor539Source.source.poly i) 841425 168285 17592186044416
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor539Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 5 17) (CoreQuotient.fused G u 5 17) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 5 17 WideAnchor539Source.data
    WideAnchor539Source.path_checked WideAnchor539Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor539Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 17 5) (CoreQuotient.fused G u 17 5) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 17 5 WideAnchor539Source.data
    WideAnchor539Source.path_swapped WideAnchor539Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor539Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor539Cell014
