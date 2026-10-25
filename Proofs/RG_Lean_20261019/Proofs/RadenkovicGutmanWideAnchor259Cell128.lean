/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor259Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor259Cell128
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (104153/2048)
  b := (249967/4096)
  s := [(4377515714419/1152921504606846976),(-5016914683127/2305843009213693952),(665152593013/1152921504606846976)]
  L := [(9451957246860929722345/9444732965739290427392),(-4011636683/13194139533312),(593679097/6597069766656),(-18179329/824633720832),(1413647/412316860416)]
  c := (550048409433/549755813888)
  R := (13302165317/50000000000000)
  total := (3243795392487/1000000000000000)
  k := 0
  n := 32
  sFloor := (633552741467/576460752303423488)
  nFloor := 66343568619411271870867497107803718858615651444281803260008527781211994455419913964970413820119941850934681446852602306535623499452514304
  eFloor := 66292357567206604813972862953631212001342530841454055650323489726373487395614779072140879297837748738669503421858694240924691532382994432
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=208306,width:=41661,den:=4096,localDen:=28334198897217871282176,lowerC:=28349279156778634838016,s:=[107581826197561344,-61647847626264576,16346790125887488],L:=[28355871740582789167035,-8614924178459459584,2549832305933811712,-624636988145795072,97145082129416192],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor259Source.source.poly i) 208306 41661 4096
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor259Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 36) (CoreQuotient.fused G u 0 36) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 36 WideAnchor259Source.data
    WideAnchor259Source.path_checked WideAnchor259Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor259Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 36 0) (CoreQuotient.fused G u 36 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 36 0 WideAnchor259Source.data
    WideAnchor259Source.path_swapped WideAnchor259Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor259Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor259Cell128
