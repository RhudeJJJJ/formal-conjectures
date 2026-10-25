/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor262Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor262Cell015
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (504855/8796093022208)
  b := (302913/4398046511104)
  s := [(2199023254909/2199023255552),(-257/2199023255552),(-13/1099511627776)]
  L := [(5800227258865/37778931862957161709568),(6960272708575/113336795588871485128704),(348013635001/56668397794435742564352),(-7/7083549724304467820544),(-1/3541774862152233910272)]
  c := (362514203679/2361183241434822606848)
  R := (-141232002041999/12500000000000)
  total := (-128621043/1000000000000000)
  k := 33
  n := 32
  sFloor := (1099511627313/2199023255552)
  nFloor := (58563079769/1208925819614629174706176)
  eFloor := (1783752940127/38685626227668133590597632)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=504855,width:=100971,den:=8796093022208,localDen:=113336795588871485128704,lowerC:=17400681776592,s:=[113336795555731517472768,-13245679140864,-1340029796352],L:=[17400681776595,6960272708575,696027270002,-112,-32],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor262Source.source.poly i) 504855 100971 8796093022208
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor262Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 3) (CoreQuotient.fused G u 0 3) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 3 WideAnchor262Source.data
    WideAnchor262Source.path_checked WideAnchor262Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor262Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 3 0) (CoreQuotient.fused G u 3 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 3 0 WideAnchor262Source.data
    WideAnchor262Source.path_swapped WideAnchor262Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor262Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor262Cell015
