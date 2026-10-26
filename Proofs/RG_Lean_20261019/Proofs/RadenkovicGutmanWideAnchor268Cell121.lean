/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor268Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor268Cell121
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (116269/8192)
  b := (558091/32768)
  s := [(3103086577933/18014398509481984),(-440843814003/4503599627370496),(116082096537/4503599627370496)]
  L := [(297937488004196355333/295147905179352825856),(-12073004267/3298534883328),(577738563/549755813888),(-102927227/412316860416),(651501/17179869184)]
  c := (1106801999439/1099511627776)
  R := (330433448203/100000000000000)
  total := (5595857520069/500000000000000)
  k := 0
  n := 32
  sFloor := (1804039708069/36028797018963968)
  nFloor := 1275050776056710729597515714936402711872375115500510244072354010171672423785935552161308647205021883209260990464
  eFloor := 1262677380161998449351660192696722622487729476618870525769165796447295993462832031955856946294635299431421837312
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=465076,width:=93015,den:=32768,localDen:=885443715538058477568,lowerC:=891314698263359127552,s:=[152522911478562816,-86673420583501824,22822668835946496],L:=[893812464012589065999,-3240822405702090752,930513087646138368,-221034536916484096,33578105859735552],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor268Source.source.poly i) 465076 93015 32768
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor268Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 44) (CoreQuotient.fused G u 0 44) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 44 WideAnchor268Source.data
    WideAnchor268Source.path_checked WideAnchor268Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor268Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 44 0) (CoreQuotient.fused G u 44 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 44 0 WideAnchor268Source.data
    WideAnchor268Source.path_swapped WideAnchor268Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor268Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor268Cell121
