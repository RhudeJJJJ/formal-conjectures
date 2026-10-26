/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor432Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor432Cell031
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (583371/549755813888)
  b := (700045/549755813888)
  s := [(2199023255447/2199023255552),(-87/4398046511104),(-3/2199023255552)]
  L := [(157690272984712868052223179/10633823966279326983230456482242756608),(448181943607/75557863725914323419136),(44818117509/75557863725914323419136),(1/2361183241434822606848),(-1/4722366482869645213696)]
  c := (1120456779693/75557863725914323419136)
  R := (-1246721408272621/100000000000000)
  total := (-1313004407/500000000000000)
  k := 36
  n := 32
  sFloor := (274877906925/549755813888)
  nFloor := (1347678806345/75557863725914323419136)
  eFloor := (1084825718021/37778931862957161709568)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=583371,width:=116674,den:=549755813888,localDen:=10633823966279326983230456482242756608,lowerC:=157690272984691897798754304,s:=[10633823965771578138992312228866162688,-210353092612945476398874624,-14507109835375550096474112],L:=[157690272984712868052223179,63076001069458432873988096,6307589291030609450237952,4503599627370496,-2251799813685248],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor432Source.source.poly i) 583371 116674 549755813888
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor432Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 8) (CoreQuotient.fused G u 2 8) (((32/17) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (32/17) 2 8 WideAnchor432Source.data
    WideAnchor432Source.path_checked WideAnchor432Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor432Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 8 2) (CoreQuotient.fused G u 8 2) (((32/17) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (32/17) 8 2 WideAnchor432Source.data
    WideAnchor432Source.path_swapped WideAnchor432Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor432Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor432Cell031
