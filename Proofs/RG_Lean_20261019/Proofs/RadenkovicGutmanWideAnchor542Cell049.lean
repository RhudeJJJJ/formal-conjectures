/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor542Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor542Cell049
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (970699/34359738368)
  b := (582419/17179869184)
  s := [(4397907582903/4398046511104),(-27784239/2199023255552),(-1388849/1099511627776)]
  L := [(294705366673/18014398509481984),(471511277387/72057594037927936),(70717180811/108086391056891904),(-76821/4503599627370496),(-5759/6755399441055744)]
  c := (294705366673/18014398509481984)
  R := (-551035290654083/100000000000000)
  total := (-15302474109/500000000000000)
  k := 16
  n := 32
  sFloor := (1099461614757/2199023255552)
  nFloor := (220302856115/4611686018427387904)
  eFloor := (850783968699/18446744073709551616)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=970699,width:=194139,den:=34359738368,localDen:=216172782113783808,lowerC:=3536464400076,s:=[216165953514848256,-2731301830656,-273058824192],L:=[3536464400076,1414533832161,141434361622,-3687408,-184288],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor542Source.source.poly i) 970699 194139 34359738368
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor542Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 5 20) (CoreQuotient.fused G u 5 20) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 5 20 WideAnchor542Source.data
    WideAnchor542Source.path_checked WideAnchor542Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor542Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 20 5) (CoreQuotient.fused G u 20 5) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 20 5 WideAnchor542Source.data
    WideAnchor542Source.path_swapped WideAnchor542Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor542Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor542Cell049
