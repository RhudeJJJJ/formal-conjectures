/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor254Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor254Cell113
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (865297/262144)
  b := (259589/65536)
  s := [(1534556922063/140737488355328),(-3061767573191/562949953421312),(361212384561/281474976710656)]
  L := [(331570541204339498089/295147905179352825856),(-453533882939/13194139533312),(39287311499/6597069766656),(-510046189/824633720832),(6155485/412316860416)]
  c := (601643134225/549755813888)
  R := (901902643511/20000000000000)
  total := (6771622569539/200000000000000)
  k := 0
  n := 32
  sFloor := (1899442442091/562949953421312)
  nFloor := 1162376237168525139746521814550492217344
  eFloor := 1012370035351306509152297612103777255424
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=865297,width:=173059,den:=262144,localDen:=885443715538058477568,lowerC:=969014094509742489600,s:=[9654597354654793728,-4815743992239489024,1136275912060305408],L:=[994711623613018494267,-30436143669545271296,5273053688624054272,-547657925301108736,13218803383009280],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor254Source.source.poly i) 865297 173059 262144
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor254Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 31) (CoreQuotient.fused G u 0 31) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 31 WideAnchor254Source.data
    WideAnchor254Source.path_checked WideAnchor254Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor254Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 31 0) (CoreQuotient.fused G u 31 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 31 0 WideAnchor254Source.data
    WideAnchor254Source.path_swapped WideAnchor254Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor254Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor254Cell113
