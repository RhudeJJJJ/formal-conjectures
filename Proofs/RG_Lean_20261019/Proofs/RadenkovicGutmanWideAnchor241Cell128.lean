/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor241Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor241Cell128
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (104153/2048)
  b := (249967/4096)
  s := [(4377515714419/1152921504606846976),(-5016914683127/2305843009213693952),(665152593013/1152921504606846976)]
  L := [(4725978623189626326705/4722366482869645213696),(-4011636683/13194139533312),(593679097/6597069766656),(-18179329/824633720832),(1413647/412316860416)]
  c := (550048409405/549755813888)
  R := (26604328089/100000000000000)
  total := (1621897566657/500000000000000)
  k := 0
  n := 32
  sFloor := (633552741467/576460752303423488)
  nFloor := 283494485859716695800859416106348294478962851301097098012510590370447686362121048790476521472
  eFloor := 283275654536313081134188711460782733015709767931685617889194504732175490361719673801402220544
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=208306,width:=41661,den:=4096,localDen:=14167099448608935641088,lowerC:=14174639577667762913280,s:=[53790913098780672,-30823923813132288,8173395062943744],L:=[14177935869568878980115,-4307462089229729792,1274916152966905856,-312318494072897536,48572541064708096],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor241Source.source.poly i) 208306 41661 4096
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor241Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 23) (CoreQuotient.fused G u 0 23) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 23 WideAnchor241Source.data
    WideAnchor241Source.path_checked WideAnchor241Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor241Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 23 0) (CoreQuotient.fused G u 23 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 23 0 WideAnchor241Source.data
    WideAnchor241Source.path_swapped WideAnchor241Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor241Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor241Cell128
