/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor519Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor519Cell033
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (420027/274877906944)
  b := (15751/8589934592)
  s := [(2199023255429/2199023255552),(-25/1099511627776),(-1/549755813888)]
  L := [(2638042853197/151115727451828646838272),(527606058389/75557863725914323419136),(79140531935/113336795588871485128704),(-1/4722366482869645213696),(1/7083549724304467820544)]
  c := (659510713299/37778931862957161709568)
  R := (-619281862211159/50000000000000)
  total := (-3756509601/1000000000000000)
  k := 36
  n := 32
  sFloor := (2199023255375/4398046511104)
  nFloor := (596588027823/18889465931478580854784)
  eFloor := (238694513375/4722366482869645213696)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=420027,width:=84005,den:=274877906944,localDen:=453347182355485940514816,lowerC:=7914128559588,s:=[453347182330128453599232,-10307921510400,-824633720832],L:=[7914128559591,3165636350334,316562127740,-96,64],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor519Source.source.poly i) 420027 84005 274877906944
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor519Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 4) (CoreQuotient.fused G u 4 4) (((15/8) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (15/8) 4 4 WideAnchor519Source.data
    WideAnchor519Source.path_checked WideAnchor519Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor519Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 4) (CoreQuotient.fused G u 4 4) (((15/8) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (15/8) 4 4 WideAnchor519Source.data
    WideAnchor519Source.path_swapped WideAnchor519Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor519Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor519Cell033
