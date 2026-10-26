/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor536Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor536Cell054
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (603851/8589934592)
  b := (724621/8589934592)
  s := [(4397270350951/4398046511104),(-310383025/4398046511104),(-15496785/2199023255552)]
  L := [(115519026780943154193679053/1267650600228229401496703205376),(2626114239449/72057594037927936),(131209520373/36028797018963968),(-2398359/4503599627370496),(-59777/2251799813685248)]
  c := (1641624106425/18014398509481984)
  R := (-232581014342723/50000000000000)
  total := (-64081798297/1000000000000000)
  k := 14
  n := 32
  sFloor := (1099232243589/2199023255552)
  nFloor := (1080001773181/4611686018427387904)
  eFloor := (522926162609/2305843009213693952)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=603851,width:=120770,den:=8589934592,localDen:=1267650600228229401496703205376,lowerC:=115519026780907085443891200,s:=[1267426887295376241358268268544,-89461816046856150030745600,-8933288339384408557486080],L:=[115519026780943154193679053,46199090274276835573366784,4616524586400814869774336,-675078043668792213504,-33651459365665767424],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor536Source.source.poly i) 603851 120770 8589934592
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor536Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 5 14) (CoreQuotient.fused G u 5 14) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 5 14 WideAnchor536Source.data
    WideAnchor536Source.path_checked WideAnchor536Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor536Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 14 5) (CoreQuotient.fused G u 14 5) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 14 5 WideAnchor536Source.data
    WideAnchor536Source.path_swapped WideAnchor536Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor536Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor536Cell054
