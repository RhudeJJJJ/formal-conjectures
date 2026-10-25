/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor019Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor019Cell056
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (869545/8589934592)
  b := (521727/4294967296)
  s := [(4397201224867/4398046511104),(-169008575/2199023255552),(-8436927/1099511627776)]
  L := [(130017342854627561274402991/1267650600228229401496703205376),(4433471422285/108086391056891904),(221492267903/54043195528445952),(-4530499/6755399441055744),(-112883/3377699720527872)]
  c := (1847657569763/18014398509481984)
  R := (-459250398800303/100000000000000)
  total := (-45540544957/500000000000000)
  k := 14
  n := 32
  sFloor := (549603682501/1099511627776)
  nFloor := (1026733692455/1152921504606846976)
  eFloor := (962081391787/1152921504606846976)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=869545,width:=173909,den:=8589934592,localDen:=3802951800684688204490109616128,lowerC:=390052028563730766439120896,s:=[3802220889174549079606526214144,-292280430870688713985228800,-29181343713294394910048256],L:=[390052028563882683823208973,155988908166878663404421120,15586132737396826116718592,-2550444201025300594688,-127094959184115924992],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor019Source.source.poly i) 869545 173909 8589934592
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor019Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 28) (CoreQuotient.fused G u 9 28) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 28 WideAnchor019Source.data
    WideAnchor019Source.path_checked WideAnchor019Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor019Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 28 9) (CoreQuotient.fused G u 28 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 28 9 WideAnchor019Source.data
    WideAnchor019Source.path_swapped WideAnchor019Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor019Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor019Cell056
