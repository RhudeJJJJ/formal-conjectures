/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor238Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor238Cell031
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (583371/549755813888)
  b := (700045/549755813888)
  s := [(4398046510543/4398046511104),(-111/2199023255552),(-3/549755813888)]
  L := [(182780518624271798145782389/2658455991569831745807614120560689152),(3116955530363/113336795588871485128704),(51949169727/18889465931478580854784),(5/3541774862152233910272),(-1/1180591620717411303424)]
  c := (1298733697469/18889465931478580854784)
  R := (-292506006682913/25000000000000)
  total := (-307904363/125000000000000)
  k := 34
  n := 32
  sFloor := (549755813787/1099511627776)
  nFloor := (531647164099/9444732965739290427392)
  eFloor := (985055821289/18889465931478580854784)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=583371,width:=116674,den:=549755813888,localDen:=7975367974709495237422842361682067456,lowerC:=548341555872646395378794496,s:=[7975367973692184160217131911166820352,-402572297931671515177156608,-43521329506126650289422336],L:=[548341555872815394437347167,219336246329268961418412032,21933587008567861070266368,11258999068426240,-6755399441055744],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor238Source.source.poly i) 583371 116674 549755813888
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor238Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 20) (CoreQuotient.fused G u 0 20) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 20 WideAnchor238Source.data
    WideAnchor238Source.path_checked WideAnchor238Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor238Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 20 0) (CoreQuotient.fused G u 20 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 20 0 WideAnchor238Source.data
    WideAnchor238Source.path_swapped WideAnchor238Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor238Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor238Cell031
