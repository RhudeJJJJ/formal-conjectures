/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor508Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor508Cell027
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (562665/1099511627776)
  b := (337599/549755813888)
  s := [(4398046510115/4398046511104),(-393/4398046511104),(-21/2199023255552)]
  L := [(754452778215/9444732965739290427392),(3621373333777/113336795588871485128704),(181068666383/56668397794435742564352),(-13/7083549724304467820544),(1/3541774862152233910272)]
  c := (754452778215/9444732965739290427392)
  R := (-1162524282726959/100000000000000)
  total := (-1180228953/1000000000000000)
  k := 34
  n := 32
  sFloor := (274877906855/549755813888)
  nFloor := (1256298426999/75557863725914323419136)
  eFloor := (883510205933/37778931862957161709568)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=562665,width:=112533,den:=1099511627776,localDen:=113336795588871485128704,lowerC:=9053433338580,s:=[113336795563385149194240,-10127532883968,-1082331758592],L:=[9053433338580,3621373333777,362137332766,-208,32],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor508Source.source.poly i) 562665 112533 1099511627776
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor508Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 38) (CoreQuotient.fused G u 4 38) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 4 38 WideAnchor508Source.data
    WideAnchor508Source.path_checked WideAnchor508Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor508Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 38 4) (CoreQuotient.fused G u 38 4) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 38 4 WideAnchor508Source.data
    WideAnchor508Source.path_swapped WideAnchor508Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor508Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor508Cell027
