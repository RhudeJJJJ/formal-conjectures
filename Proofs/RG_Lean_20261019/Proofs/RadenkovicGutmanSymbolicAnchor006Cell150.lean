/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanSymbolicAnchor006Source
namespace Gebendorfer.RadenkovicGutman.SymbolicAnchor006Cell150
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1617619/268435456)
  b := (444845/67108864)
  s := [(2002317924233/4398046511104),(-18831668985/549755813888),(5052943629/2199023255552)]
  L := [(5004281819516980131123/9444732965739290427392),(1208408736833/26388279066624),(-10028171537/4398046511104),(103124623/1649267441664),(405209/274877906944)]
  c := (1165150157063/2199023255552)
  R := (-31758165906717/100000000000000)
  total := (-179114139731/1000000000000000)
  k := 1
  n := 32
  sFloor := (1861770459611/8796093022208)
  nFloor := (786235558523/281474976710656)
  eFloor := (69429418663/35184372088832)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1617619,width:=161761,den:=268435456,localDen:=28334198897217871282176,lowerC:=15012845458544545234944,s:=[12899835001163011325952,-970576829036070174720,65106682905259671552],L:=[15012845458550940393369,1297519001224601403392,-64606003185139580928,1771667532789317632,41768625673076736],transformed:=fun i => IntegerPolynomialPaymentCell.affine (SymbolicAnchor006Source.source.poly i) 1617619 161761 268435456
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
end Gebendorfer.RadenkovicGutman.SymbolicAnchor006Cell150
