/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor017Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor017Cell087
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (483767/16777216)
  b := (72565/2097152)
  s := [(4649084133105/17592186044416),(-160874749657/8796093022208),(20108268089/4398046511104)]
  L := [(92709261160878037987/147573952589676412928),(764710143031/26388279066624),(-33032767731/4398046511104),(2169928499/1649267441664),(-41870001/274877906944)]
  c := (86342227795/137438953472)
  R := (-5810763142429/25000000000000)
  total := (-1284719767137/1000000000000000)
  k := 1
  n := 32
  sFloor := (137742740817/1099511627776)
  nFloor := (747515442483/8796093022208)
  eFloor := (1384890666867/17592186044416)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=483767,width:=96753,den:=16777216,localDen:=442721857769029238784,lowerC:=278127783482480394240,s:=[116998033054913003520,-8097091271824244736,2024164542690361344],L:=[278127783482634113961,12829707247021981696,-3325187275804901376,582485746116460544,-67436356866932736],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor017Source.source.poly i) 483767 96753 16777216
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor017Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 26) (CoreQuotient.fused G u 9 26) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 26 WideAnchor017Source.data
    WideAnchor017Source.path_checked WideAnchor017Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor017Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 26 9) (CoreQuotient.fused G u 26 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 26 9 WideAnchor017Source.data
    WideAnchor017Source.path_swapped WideAnchor017Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor017Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor017Cell087
