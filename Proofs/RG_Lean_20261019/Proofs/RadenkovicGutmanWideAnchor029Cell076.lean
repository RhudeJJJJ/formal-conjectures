/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor029Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor029Cell076
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (130219/33554432)
  b := (625051/134217728)
  s := [(101026617761/137438953472),(-4554075051/68719476736),(7297981457/2199023255552)]
  L := [(198985503747861325337/1180591620717411303424),(1280784650333/26388279066624),(-3322155115/13194139533312),(-1247368765/3298534883328),(9177301/206158430208)]
  c := (370639383323/2199023255552)
  R := (-89026949436049/100000000000000)
  total := (-640161834253/1000000000000000)
  k := 3
  n := 32
  sFloor := (1477993464001/4398046511104)
  nFloor := (1902397714587/1125899906842624)
  eFloor := (861732352551/562949953421312)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=520876,width:=104175,den:=134217728,localDen:=3541774862152233910272,lowerC:=596956511243209801728,s:=[2603436115853926465536,-234715240890894385152,11754221881736036352],L:=[596956511243583976011,171904005824969703424,-891784223197757440,-1339352012931727360,157664830642192384],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor029Source.source.poly i) 520876 104175 134217728
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
end Gebendorfer.RadenkovicGutman.WideAnchor029Cell076
