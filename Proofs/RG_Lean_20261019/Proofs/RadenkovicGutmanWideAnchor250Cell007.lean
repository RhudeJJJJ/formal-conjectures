/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor250Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor250Cell007
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (939307/70368744177664)
  b := (4403/274877906944)
  s := [(4398046511103/4398046511104)]
  L := [(119778026757307162181310801/87112285931760246646623899502532662132736),(2723431219303/4951760157141521099596496896),(408513812969/7427640235712281649394745344),(7/309485009821345068724781056),(-5/464227514732017603087171584)]
  c := (1702148136321/1237940039285380274899124224)
  R := (-68440668142973/4000000000000)
  total := (-45428187/1000000000000000)
  k := 50
  n := 32
  sFloor := (2199023255551/4398046511104)
  nFloor := (2021624303049/618970019642690137449562112)
  eFloor := (587333471481/309485009821345068724781056)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=939307,width:=187861,den:=70368744177664,localDen:=261336857795280739939871698507597986398208,lowerC:=359334080271779991946002432,s:=[261336857795221318817986000254402828435456],L:=[359334080271921486543932403,143733326067447262183686144,14373301998928819501662208,5910974510923776,-2814749767106560],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor250Source.source.poly i) 939307 187861 70368744177664
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor250Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 2) (CoreQuotient.fused G u 0 2) (((15/8) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (15/8) 0 2 WideAnchor250Source.data
    WideAnchor250Source.path_checked WideAnchor250Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor250Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 0) (CoreQuotient.fused G u 2 0) (((15/8) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (15/8) 2 0 WideAnchor250Source.data
    WideAnchor250Source.path_swapped WideAnchor250Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor250Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor250Cell007
