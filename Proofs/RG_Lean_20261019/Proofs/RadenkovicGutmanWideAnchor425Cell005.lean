/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor425Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor425Cell005
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (652297/70368744177664)
  b := (195689/17592186044416)
  s := [(4398046511103/4398046511104)]
  L := [(4678115924055/4951760157141521099596496896),(5613721896629/14855280471424563298789490688),(280685234255/7427640235712281649394745344),(-5/928455029464035206174343168),(1/464227514732017603087171584)]
  c := (1169528981013/1237940039285380274899124224)
  R := (-1729781202352243/100000000000000)
  total := (-31895227/1000000000000000)
  k := 50
  n := 32
  sFloor := (2199023255551/4398046511104)
  nFloor := (122537591919/77371252455336267181195264)
  eFloor := (145552466007/77371252455336267181195264)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=652297,width:=130459,den:=70368744177664,localDen:=14855280471424563298789490688,lowerC:=14034347772156,s:=[14855280471421185599068962816],L:=[14034347772165,5613721896629,561370468510,-80,32],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor425Source.source.poly i) 652297 130459 70368744177664
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor425Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 6) (CoreQuotient.fused G u 2 6) (((36/19) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (36/19) 2 6 WideAnchor425Source.data
    WideAnchor425Source.path_checked WideAnchor425Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor425Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 6 2) (CoreQuotient.fused G u 6 2) (((36/19) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (36/19) 6 2 WideAnchor425Source.data
    WideAnchor425Source.path_swapped WideAnchor425Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor425Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor425Cell005
