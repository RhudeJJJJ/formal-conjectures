/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor248Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor248Cell005
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (652297/70368744177664)
  b := (195689/17592186044416)
  s := [(4398046511103/4398046511104)]
  L := [(3879871466765/4951760157141521099596496896),(4655831484901/14855280471424563298789490688),(232790860453/7427640235712281649394745344),(5/928455029464035206174343168),(-1/464227514732017603087171584)]
  c := (969967866691/1237940039285380274899124224)
  R := (-434783968370283/25000000000000)
  total := (-32068657/1000000000000000)
  k := 51
  n := 32
  sFloor := (2199023255551/4398046511104)
  nFloor := (577001174719/309485009821345068724781056)
  eFloor := (1180098005299/1237940039285380274899124224)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=652297,width:=130459,den:=70368744177664,localDen:=14855280471424563298789490688,lowerC:=11639614400292,s:=[14855280471421185599068962816],L:=[11639614400295,4655831484901,465581720906,80,-32],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor248Source.source.poly i) 652297 130459 70368744177664
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor248Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 2) (CoreQuotient.fused G u 0 2) (((48/25) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (48/25) 0 2 WideAnchor248Source.data
    WideAnchor248Source.path_checked WideAnchor248Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor248Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 0) (CoreQuotient.fused G u 2 0) (((48/25) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (48/25) 2 0 WideAnchor248Source.data
    WideAnchor248Source.path_swapped WideAnchor248Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor248Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor248Cell005
