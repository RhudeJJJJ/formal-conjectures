/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanSymbolicAnchor006Source
namespace Gebendorfer.RadenkovicGutman.SymbolicAnchor006Cell145
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (2008831/536870912)
  b := (1104857/268435456)
  s := [(5541121691065/8796093022208),(-327745188653/8796093022208),(6891160313/4398046511104)]
  L := [(759199148467606728613/2361183241434822606848),(2095913294489/52776558133248),(-6929426913/8796093022208),(-159793115/3298534883328),(3146149/549755813888)]
  c := (1414118611193/4398046511104)
  R := (-3545793813083/6250000000000)
  total := (-100659744919/500000000000000)
  k := 2
  n := 32
  sFloor := (1306789705759/4398046511104)
  nFloor := (302390319013/281474976710656)
  eFloor := (427025918173/562949953421312)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=2008831,width:=200883,den:=536870912,localDen:=7083549724304467820544,lowerC:=2277597445402077954048,s:=[4462300583677573201920,-263935287503622242304,11098990565935546368],L:=[2277597445402820185839,281308720471308500992,-5580311619629481984,-343153101525483520,40537821190029312],transformed:=fun i => IntegerPolynomialPaymentCell.affine (SymbolicAnchor006Source.source.poly i) 2008831 200883 536870912
}
theorem checked : IntegerPolynomialPaymentCell.checks SymbolicAnchor006Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 15) (CoreQuotient.fused G u 9 15) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 15 SymbolicAnchor006Source.data
    SymbolicAnchor006Source.path_checked SymbolicAnchor006Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry SymbolicAnchor006Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 15 9) (CoreQuotient.fused G u 15 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 15 9 SymbolicAnchor006Source.data
    SymbolicAnchor006Source.path_swapped SymbolicAnchor006Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry SymbolicAnchor006Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.SymbolicAnchor006Cell145
