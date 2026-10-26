/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor024Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor024Cell048
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (202229/8589934592)
  b := (970699/34359738368)
  s := [(1099468764395/1099511627776),(-68577413/4398046511104),(-3427781/2199023255552)]
  L := [(4172571733673/144115188075855872),(1251719721829/108086391056891904),(125151718187/108086391056891904),(-251221/6755399441055744),(-12551/6755399441055744)]
  c := (521571466709/18014398509481984)
  R := (-52249178037849/10000000000000)
  total := (-2416023229/100000000000000)
  k := 16
  n := 32
  sFloor := (1099449906151/2199023255552)
  nFloor := (678090572623/9223372036854775808)
  eFloor := (1826075397941/36893488147419103232)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=808916,width:=161783,den:=34359738368,localDen:=432345564227567616,lowerC:=12517715201016,s:=[432328709660344320,-6741434007552,-673929166848],L:=[12517715201019,5006878887316,500606872748,-16078144,-803264],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor024Source.source.poly i) 808916 161783 34359738368
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor024Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 33) (CoreQuotient.fused G u 9 33) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 33 WideAnchor024Source.data
    WideAnchor024Source.path_checked WideAnchor024Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor024Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 33 9) (CoreQuotient.fused G u 33 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 33 9 WideAnchor024Source.data
    WideAnchor024Source.path_swapped WideAnchor024Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor024Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor024Cell048
