/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor428Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor428Cell094
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (433355/4194304)
  b := (260013/2097152)
  s := [(6875590735861/8796093022208),(-539996776853/8796093022208),(6265962951/4398046511104)]
  L := [(416283200189968426869/4722366482869645213696),(445820243843/13194139533312),(4499607775/1649267441664),(-503673209/3298534883328),(-6813149/824633720832)]
  c := (193846970885/2199023255552)
  R := (-121434976404669/100000000000000)
  total := (-4650118941391/200000000000000)
  k := 4
  n := 32
  sFloor := (1587031471227/4398046511104)
  nFloor := (29184854573/137438953472)
  eFloor := (162288400753/549755813888)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=433355,width:=86671,den:=4194304,localDen:=14167099448608935641088,lowerC:=1248849600569608765440,s:=[11073914006701338525696,-869725686198391799808,20184079464369487872],L:=[1248849600569905280607,478695841800107589632,38651336476904652800,-2163259960526372864,-117049008551100416],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor428Source.source.poly i) 433355 86671 4194304
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor428Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 6) (CoreQuotient.fused G u 2 6) (((13/7) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (13/7) 2 6 WideAnchor428Source.data
    WideAnchor428Source.path_checked WideAnchor428Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor428Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 6 2) (CoreQuotient.fused G u 6 2) (((13/7) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (13/7) 6 2 WideAnchor428Source.data
    WideAnchor428Source.path_swapped WideAnchor428Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor428Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor428Cell094
