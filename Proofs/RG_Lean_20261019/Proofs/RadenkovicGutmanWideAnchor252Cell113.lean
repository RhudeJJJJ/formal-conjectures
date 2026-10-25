/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor252Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor252Cell113
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (865297/262144)
  b := (259589/65536)
  s := [(1534556922063/140737488355328),(-3061767573191/562949953421312),(361212384561/281474976710656)]
  L := [(663141082354724686819/590295810358705651712),(-453533882903/13194139533312),(39287311385/6597069766656),(-510046165/824633720832),(6155479/412316860416)]
  c := (601643134175/549755813888)
  R := (4509513213399/100000000000000)
  total := (33858112820451/1000000000000000)
  k := 0
  n := 32
  sFloor := (1899442442091/562949953421312)
  nFloor := 7073946220692986901637835488493568000
  eFloor := 6161044037653015181013934679504453632
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=865297,width:=173059,den:=262144,localDen:=1770887431076116955136,lowerC:=1938028188858423705600,s:=[19309194709309587456,-9631487984478978048,2272551824120610816],L:=[1989423247064174060457,-60872287334258704384,10546107346646466560,-1095315799062609920,26437580996214784],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor252Source.source.poly i) 865297 173059 262144
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor252Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 29) (CoreQuotient.fused G u 0 29) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 29 WideAnchor252Source.data
    WideAnchor252Source.path_checked WideAnchor252Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor252Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 29 0) (CoreQuotient.fused G u 29 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 29 0 WideAnchor252Source.data
    WideAnchor252Source.path_swapped WideAnchor252Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor252Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor252Cell113
