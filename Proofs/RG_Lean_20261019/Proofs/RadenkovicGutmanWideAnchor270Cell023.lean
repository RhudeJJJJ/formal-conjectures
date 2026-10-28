/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor270Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor270Cell023
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1085389/4398046511104)
  b := (651233/2199023255552)
  s := [(4398046510517/4398046511104),(-235/4398046511104),(-11/2199023255552)]
  L := [(4568513386707/75557863725914323419136),(1827398619631/75557863725914323419136),(91369594183/37778931862957161709568),(-7/4722366482869645213696),(1/2361183241434822606848)]
  c := (285532086669/4722366482869645213696)
  R := (-1176448837647819/100000000000000)
  total := (-36002529/62500000000000)
  k := 34
  n := 32
  sFloor := (1099511627565/2199023255552)
  nFloor := (811758372973/151115727451828646838272)
  eFloor := (55907784779/9444732965739290427392)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1085389,width:=217077,den:=4398046511104,localDen:=75557863725914323419136,lowerC:=4568513386704,s:=[75557863715829740208128,-4037269258240,-377957122048],L:=[4568513386707,1827398619631,182739188366,-112,32],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor270Source.source.poly i) 1085389 217077 4398046511104
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor270Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 46) (CoreQuotient.fused G u 0 46) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 46 WideAnchor270Source.data
    WideAnchor270Source.path_checked WideAnchor270Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor270Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 46 0) (CoreQuotient.fused G u 46 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 46 0 WideAnchor270Source.data
    WideAnchor270Source.path_swapped WideAnchor270Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor270Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor270Cell023
