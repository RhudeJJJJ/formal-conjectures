/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor238Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor238Cell128
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (104153/2048)
  b := (249967/4096)
  s := [(4377515714419/1152921504606846976),(-5016914683131/2305843009213693952),(665152593015/1152921504606846976)]
  L := [(4725978623109523838219/4722366482869645213696),(-4011636683/13194139533312),(593679097/6597069766656),(-18179329/824633720832),(1413647/412316860416)]
  c := (137512102349/137438953472)
  R := (26604327271/100000000000000)
  total := (3243795047117/1000000000000000)
  k := 0
  n := 32
  sFloor := (633552741467/576460752303423488)
  nFloor := 16348802657595044541285832367027254484657905193844045567325051581060581515564417024
  eFloor := 16336182905530596758423112165221597349123942415252874884046720979883334353874321408
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=208306,width:=41661,den:=4096,localDen:=14167099448608935641088,lowerC:=14174639577435834679296,s:=[53790913098780672,-30823923813156864,8173395062968320],L:=[14177935869328571514657,-4307462089229729792,1274916152966905856,-312318494072897536,48572541064708096],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor238Source.source.poly i) 208306 41661 4096
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor238Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 20) (CoreQuotient.fused G u 0 20) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 20 WideAnchor238Source.data
    WideAnchor238Source.path_checked WideAnchor238Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor238Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 20 0) (CoreQuotient.fused G u 20 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 20 0 WideAnchor238Source.data
    WideAnchor238Source.path_swapped WideAnchor238Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor238Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor238Cell128
