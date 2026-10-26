/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor510Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor510Cell092
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1203765/16777216)
  b := (722259/8388608)
  s := [(5240323094297/8796093022208),(-131206029127/4398046511104),(3234678847/2199023255552)]
  L := [(599465051641425981207/2361183241434822606848),(1986557454101/52776558133248),(-28731535313/26388279066624),(211317673/3298534883328),(-9747979/1649267441664)]
  c := (1116590670573/4398046511104)
  R := (-1071000366359/1562500000000)
  total := (-9337560554173/1000000000000000)
  k := 2
  n := 32
  sFloor := (1247712437857/4398046511104)
  nFloor := (604725722537/274877906944)
  eFloor := (1206789893041/549755813888)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1203765,width:=240753,den:=16777216,localDen:=7083549724304467820544,lowerC:=1798395154923654217728,s:=[4220065558214838583296,-211322101551933161472,10419629895695990784],L:=[1798395154924277943621,266631228030900502528,-7712562783325257728,453801247300911104,-41867251007094784],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor510Source.source.poly i) 1203765 240753 16777216
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor510Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 40) (CoreQuotient.fused G u 4 40) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 4 40 WideAnchor510Source.data
    WideAnchor510Source.path_checked WideAnchor510Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor510Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 40 4) (CoreQuotient.fused G u 40 4) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 40 4 WideAnchor510Source.data
    WideAnchor510Source.path_swapped WideAnchor510Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor510Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor510Cell092
