/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor258Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor258Cell020
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1256239/8796093022208)
  b := (753743/4398046511104)
  s := [(274877906937/274877906944),(-43/4398046511104),(-3/2199023255552)]
  L := [(4236348169617/302231454903657293676544),(5083601616541/906694364710971881029632),(84726423793/151115727451828646838272),(11/56668397794435742564352),(-1/9444732965739290427392)]
  c := (264771760601/18889465931478580854784)
  R := (-624768933759241/50000000000000)
  total := (-11069817/31250000000000)
  k := 37
  n := 32
  sFloor := (2199023255471/4398046511104)
  nFloor := (265030457835/151115727451828646838272)
  eFloor := (238900152653/151115727451828646838272)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1256239,width:=251247,den:=8796093022208,localDen:=906694364710971881029632,lowerC:=12709044508848,s:=[906694364687882136846336,-8864812498944,-1236950581248],L:=[12709044508851,5083601616541,508358542758,176,-96],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor258Source.source.poly i) 1256239 251247 8796093022208
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor258Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 35) (CoreQuotient.fused G u 0 35) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 35 WideAnchor258Source.data
    WideAnchor258Source.path_checked WideAnchor258Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor258Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 35 0) (CoreQuotient.fused G u 35 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 35 0 WideAnchor258Source.data
    WideAnchor258Source.path_swapped WideAnchor258Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor258Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor258Cell020
