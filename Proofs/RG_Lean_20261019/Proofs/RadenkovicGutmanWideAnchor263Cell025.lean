/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor263Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor263Cell025
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1562959/4398046511104)
  b := (937775/2199023255552)
  s := [(4398046510505/4398046511104),(-237/4398046511104),(-13/2199023255552)]
  L := [(1422427002267/18889465931478580854784),(1137938689241/37778931862957161709568),(170690366335/56668397794435742564352),0,(-1/3541774862152233910272)]
  c := (1422427002267/18889465931478580854784)
  R := (-1165475283815703/100000000000000)
  total := (-82169913/100000000000000)
  k := 34
  n := 32
  sFloor := (2199023255121/4398046511104)
  nFloor := (225445817955/18889465931478580854784)
  eFloor := (814489715467/75557863725914323419136)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1562959,width:=312591,den:=4398046511104,localDen:=113336795588871485128704,lowerC:=8534562013602,s:=[113336795573435372666880,-6107443494912,-670014898176],L:=[8534562013602,3413816067723,341380732670,0,-32],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor263Source.source.poly i) 1562959 312591 4398046511104
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor263Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 39) (CoreQuotient.fused G u 0 39) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 39 WideAnchor263Source.data
    WideAnchor263Source.path_checked WideAnchor263Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor263Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 39 0) (CoreQuotient.fused G u 39 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 39 0 WideAnchor263Source.data
    WideAnchor263Source.path_swapped WideAnchor263Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor263Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor263Cell025
