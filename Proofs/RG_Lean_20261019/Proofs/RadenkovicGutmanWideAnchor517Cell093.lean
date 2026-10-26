/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor517Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor517Cell093
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (722259/8388608)
  b := (433355/4194304)
  s := [(1878595877285/2199023255552),(-428006590981/8796093022208),(-4297797827/4398046511104)]
  L := [(665132014286267811439/9444732965739290427392),(359959943875/13194139533312),(122775545875/52776558133248),(-622297085/6597069766656),(-18223357/3298534883328)]
  c := (154863115001/2199023255552)
  R := (-26532269683061/20000000000000)
  total := (-5322399119807/250000000000000)
  k := 4
  n := 32
  sFloor := (884722665313/2199023255552)
  nFloor := (1533163290119/8796093022208)
  eFloor := (1710776175635/8796093022208)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=722259,width:=144451,den:=8388608,localDen:=28334198897217871282176,lowerC:=1995396042857946021888,s:=[24205523566018512814080,-1378705733051882668032,-27688351667677298688],L:=[1995396042858803434317,773008093406560256000,65914619285209088000,-2672745628471132160,-156537444676665344],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor517Source.source.poly i) 722259 144451 8388608
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor517Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 4) (CoreQuotient.fused G u 4 4) (((19/10) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (19/10) 4 4 WideAnchor517Source.data
    WideAnchor517Source.path_checked WideAnchor517Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor517Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 4) (CoreQuotient.fused G u 4 4) (((19/10) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (19/10) 4 4 WideAnchor517Source.data
    WideAnchor517Source.path_swapped WideAnchor517Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor517Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor517Cell093
