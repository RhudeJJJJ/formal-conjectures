/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor543Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor543Cell126
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (144657/4096)
  b := (1388707/32768)
  s := [(1630511207801/144115188075855872),(-1866350074561/288230376151711744),(247187375065/144115188075855872)]
  L := [(591226203884375441643/590295810358705651712),(-8232063463/13194139533312),(404165211/2199023255552),(-36953891/824633720832),(954489/137438953472)]
  c := (1100719062137/1099511627776)
  R := (27438815569/50000000000000)
  total := (2321652670447/500000000000000)
  k := 0
  n := 32
  sFloor := (1889047091171/576460752303423488)
  nFloor := 1587280972200399792127221729102207510733391108317242089135381043048612733859479738860806602752
  eFloor := 1584747250099578115475108866733086121037617484462431095403545789163046772942340872582566248448
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1157256,width:=231451,den:=32768,localDen:=1770887431076116955136,lowerC:=1772832140235827576832,s:=[20035721721458688,-11466854858102784,3037438464798720],L:=[1773678611653126324929,-1104888854755672064,325476818142363648,-79357876652474368,12298497118175232],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor543Source.source.poly i) 1157256 231451 32768
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor543Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 5 21) (CoreQuotient.fused G u 5 21) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 5 21 WideAnchor543Source.data
    WideAnchor543Source.path_checked WideAnchor543Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor543Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 21 5) (CoreQuotient.fused G u 21 5) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 21 5 WideAnchor543Source.data
    WideAnchor543Source.path_swapped WideAnchor543Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor543Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor543Cell126
