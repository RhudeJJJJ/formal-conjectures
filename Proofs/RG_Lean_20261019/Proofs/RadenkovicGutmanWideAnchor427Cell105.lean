/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor427Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor427Cell105
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1609927/2097152)
  b := (241489/262144)
  s := [(1253843994941/8796093022208),(-155045637741/4398046511104),(1395351451/274877906944)]
  L := [(152145464718634174583/147573952589676412928),(1026238670813/13194139533312),(-37906162785/2199023255552),(2031043309/824633720832),(-34990731/137438953472)]
  c := (566786023671/549755813888)
  R := (30507644313/2000000000000)
  total := (2400352035259/500000000000000)
  k := 0
  n := 32
  sFloor := (988403965891/17592186044416)
  nFloor := (1026371853983/134217728)
  eFloor := (186781093831/33554432)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1609927,width:=321985,den:=2097152,localDen:=442721857769029238784,lowerC:=456436394155655036928,s:=[63108034600284192768,-15607404925431054336,2247370818176679936],L:=[456436394155902523749,34434855695565193216,-7631518569301278720,1090408073614327808,-112713033981100032],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor427Source.source.poly i) 1609927 321985 2097152
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor427Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 6) (CoreQuotient.fused G u 2 6) (((28/15) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (28/15) 2 6 WideAnchor427Source.data
    WideAnchor427Source.path_checked WideAnchor427Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor427Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 6 2) (CoreQuotient.fused G u 6 2) (((28/15) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (28/15) 6 2 WideAnchor427Source.data
    WideAnchor427Source.path_swapped WideAnchor427Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor427Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor427Cell105
