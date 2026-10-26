/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor541Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor541Cell055
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (724621/8589934592)
  b := (869545/8589934592)
  s := [(549396876897/549755813888),(-573754751/2199023255552),(-28537091/1099511627776)]
  L := [(264686045487543613072909/618970019642690137449562112),(1154739141239/6755399441055744),(7197977309/422212465065984),(-7641277/844424930131968),(-94471/211106232532992)]
  c := (1925844448033/4503599627370496)
  R := (-387863386366773/100000000000000)
  total := (-63857667881/1000000000000000)
  k := 12
  n := 32
  sFloor := (2196956678655/4398046511104)
  nFloor := (1161996152851/2305843009213693952)
  eFloor := (887367358093/2305843009213693952)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=724621,width:=144924,den:=8589934592,localDen:=1856910058928070412348686336,lowerC:=794058136462551026761728,s:=[1855697677553882597041373184,-484492815526059696979968,-48194862147689225650176],L:=[794058136462630839218727,317412278210088314863616,31657038990853208539136,-16803345825114619904,-830975703901011968],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor541Source.source.poly i) 724621 144924 8589934592
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor541Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 5 19) (CoreQuotient.fused G u 5 19) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 5 19 WideAnchor541Source.data
    WideAnchor541Source.path_checked WideAnchor541Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor541Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 19 5) (CoreQuotient.fused G u 19 5) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 19 5 WideAnchor541Source.data
    WideAnchor541Source.path_swapped WideAnchor541Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor541Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor541Cell055
