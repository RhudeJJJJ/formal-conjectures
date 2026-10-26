/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor419Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor419Cell038
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1045159/274877906944)
  b := (627095/137438953472)
  s := [(4398046509941/4398046511104),(-29/274877906944),(-3/274877906944)]
  L := [(21820189221224325999614703/166153499473114484112975882535043072),(5953581160573/113336795588871485128704),(297677918561/56668397794435742564352),(17/7083549724304467820544),(-5/3541774862152233910272)]
  c := (310083538881/2361183241434822606848)
  R := (-568833556034313/50000000000000)
  total := (-4290057443/500000000000000)
  k := 33
  n := 32
  sFloor := (1099511627357/2199023255552)
  nFloor := (306860468533/1180591620717411303424)
  eFloor := (1235510092937/4722366482869645213696)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1045159,width:=209031,den:=274877906944,localDen:=498460498419343452338927647605129216,lowerC:=65460567663665451947261952,s:=[498460498287532759069070110400446464,-52588273153236369099718656,-5440166188265831286177792],L:=[65460567663672977998844109,26184126851832585851502592,2618402662319813388402688,1196268651020288,-703687441776640],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor419Source.source.poly i) 1045159 209031 274877906944
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor419Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 4) (CoreQuotient.fused G u 2 4) (((17/9) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (17/9) 2 4 WideAnchor419Source.data
    WideAnchor419Source.path_checked WideAnchor419Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor419Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 2) (CoreQuotient.fused G u 4 2) (((17/9) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (17/9) 4 2 WideAnchor419Source.data
    WideAnchor419Source.path_swapped WideAnchor419Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor419Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor419Cell038
