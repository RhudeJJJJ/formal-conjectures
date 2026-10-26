/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor528Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor528Cell045
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (468123/34359738368)
  b := (1123495/68719476736)
  s := [(4398046477911/4398046511104),(-13279/4398046511104),(-663/2199023255552)]
  L := [(2495694904465/590295810358705651712),(5989661342419/3541774862152233910272),(299482741129/1770887431076116955136),(-163/221360928884514619392),(-1/110680464442257309696)]
  c := (155980931529/36893488147419103232)
  R := (-482039178336503/50000000000000)
  total := (-26014106557/1000000000000000)
  k := 28
  n := 32
  sFloor := (2199023231653/4398046511104)
  nFloor := (946168779993/147573952589676412928)
  eFloor := (105562443933/18446744073709551616)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=936246,width:=187249,den:=68719476736,localDen:=3541774862152233910272,lowerC:=14974169426784,s:=[3541774835421699637248,-10693663260672,-1067836243968],L:=[14974169426790,5989661342419,598965482258,-2608,-32],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor528Source.source.poly i) 936246 187249 68719476736
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor528Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 8) (CoreQuotient.fused G u 4 8) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 4 8 WideAnchor528Source.data
    WideAnchor528Source.path_checked WideAnchor528Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor528Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 8 4) (CoreQuotient.fused G u 8 4) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 8 4 WideAnchor528Source.data
    WideAnchor528Source.path_swapped WideAnchor528Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor528Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor528Cell045
