/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor260Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor260Cell102
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (931671/2097152)
  b := (1118005/2097152)
  s := [(1358661100415/4398046511104),(-104989640887/2199023255552),(17516601057/4398046511104)]
  L := [(512573662115924091203/590295810358705651712),(693859540907/6597069766656),(-32872466951/3298534883328),(67740391/412316860416),(8769455/206158430208)]
  c := (1909485690727/2199023255552)
  R := (-7058967655077/100000000000000)
  total := (-959498118143/250000000000000)
  k := 1
  n := 32
  sFloor := (583099209849/4398046511104)
  nFloor := (101104185675/2048)
  eFloor := (491795019813/16384)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=931671,width:=186334,den:=2097152,localDen:=1770887431076116955136,lowerC:=1537720986347331649536,s:=[547069218059043471360,-84548826380334268416,7053115188458815488],L:=[1537720986347772273609,186256502263321198592,-17648271311673229312,290942763963252736,75329044857487360],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor260Source.source.poly i) 931671 186334 2097152
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor260Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 37) (CoreQuotient.fused G u 0 37) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 37 WideAnchor260Source.data
    WideAnchor260Source.path_checked WideAnchor260Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor260Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 37 0) (CoreQuotient.fused G u 37 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 37 0 WideAnchor260Source.data
    WideAnchor260Source.path_swapped WideAnchor260Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor260Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor260Cell102
