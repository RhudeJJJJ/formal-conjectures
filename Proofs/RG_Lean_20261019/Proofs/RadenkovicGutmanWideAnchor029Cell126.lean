/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor029Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor029Cell126
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (144657/4096)
  b := (1388707/32768)
  s := [(1630511207801/144115188075855872),(-7465400298245/1152921504606846976),(988749500261/576460752303423488)]
  L := [(4729809631645745040243/4722366482869645213696),(-8232063463/13194139533312),(404165211/2199023255552),(-36953891/824633720832),(954489/137438953472)]
  c := (550359531135/549755813888)
  R := (2743881859/5000000000000)
  total := (2321652883601/500000000000000)
  k := 0
  n := 32
  sFloor := (1889047091171/576460752303423488)
  nFloor := 169984985059111940654255098572810925760461890148561976748514065609836321441775046734857480409199874202681470538719414003223614313330766629139988381690010533888
  eFloor := 169713643865778345688425375128389539966118196340962857853642704393795021787030616866925789041567305637788604117993611484714999200591744399267151961693613981696
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1157256,width:=231451,den:=32768,localDen:=14167099448608935641088,lowerC:=14182657123600312565760,s:=[160285773771669504,-91734838864834560,24299507718414336],L:=[14189428894937235120729,-8839110838045376512,2603814545138909184,-634863013219794944,98387976945401856],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor029Source.source.poly i) 1157256 231451 32768
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor029Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 38) (CoreQuotient.fused G u 9 38) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 38 WideAnchor029Source.data
    WideAnchor029Source.path_checked WideAnchor029Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor029Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 38 9) (CoreQuotient.fused G u 38 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 38 9 WideAnchor029Source.data
    WideAnchor029Source.path_swapped WideAnchor029Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor029Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor029Cell126
