/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor537Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor537Cell098
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (224651/1048576)
  b := (269581/1048576)
  s := [(1989644878279/8796093022208),(121755001595/17592186044416),(-31334624827/8796093022208)]
  L := [(225356098873207892995/295147905179352825856),(-2607510761/26388279066624),(124364456299/13194139533312),(-2655153445/1649267441664),(124689449/824633720832)]
  c := (839489727261/1099511627776)
  R := (-6745678643591/50000000000000)
  total := (-5704072050893/1000000000000000)
  k := 1
  n := 32
  sFloor := (1989644878279/17592186044416)
  nFloor := (1471512652675/34359738368)
  eFloor := (1216200128363/34359738368)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=224651,width:=44930,den:=1048576,localDen:=885443715538058477568,lowerC:=676046423233866498048,s:=[200284211317082947584,6128129882518978560,-3154246614009249792],L:=[676068296619623678985,-87493542519242752,8345957384203534336,-1425474651517091840,133884276402814976],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor537Source.source.poly i) 224651 44930 1048576
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor537Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 5 15) (CoreQuotient.fused G u 5 15) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 5 15 WideAnchor537Source.data
    WideAnchor537Source.path_checked WideAnchor537Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor537Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 15 5) (CoreQuotient.fused G u 15 5) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 15 5 WideAnchor537Source.data
    WideAnchor537Source.path_swapped WideAnchor537Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor537Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor537Cell098
