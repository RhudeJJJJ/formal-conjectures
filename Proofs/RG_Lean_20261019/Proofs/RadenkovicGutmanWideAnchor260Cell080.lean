/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor260Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor260Cell080
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1080087/134217728)
  b := (162013/16777216)
  s := [(4120298426537/4398046511104),(-23643047035/1099511627776),(-641638553/1099511627776)]
  L := [(683578150135853260215/18889465931478580854784),(1786178865445/140737488355328),(136536262505/211106232532992),(-824154983/8796093022208),(31350115/13194139533312)]
  c := (636631762735/17592186044416)
  R := (-165950934987539/100000000000000)
  total := (-2540627520469/1000000000000000)
  k := 5
  n := 32
  sFloor := (502894960523/1099511627776)
  nFloor := (419287784987/70368744177664)
  eFloor := (755561031531/140737488355328)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1080087,width:=216017,den:=134217728,localDen:=56668397794435742564352,lowerC:=2050734450406242385920,s:=[53089640975210020601856,-1218553365517377208320,-33069799211853152256],L:=[2050734450407559780645,719210607364936826880,36651173886065377280,-5309578048230653952,134647718650839040],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor260Source.source.poly i) 1080087 216017 134217728
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor260Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 37) (CoreQuotient.fused G u 0 37) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 37 WideAnchor260Source.data
    WideAnchor260Source.path_checked WideAnchor260Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor260Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 37 0) (CoreQuotient.fused G u 37 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 37 0 WideAnchor260Source.data
    WideAnchor260Source.path_swapped WideAnchor260Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor260Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor260Cell080
