/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor250Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor250Cell043
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (650171/68719476736)
  b := (780205/68719476736)
  s := [(4398046507573/4398046511104),(-1411/4398046511104),(-71/2199023255552)]
  L := [(3262101094637/4722366482869645213696),(3914515290689/14167099448608935641088),(195725463119/7083549724304467820544),(-17/885443715538058477568),(1/442721857769029238784)]
  c := (815525273659/1180591620717411303424)
  R := (-1054660219452883/100000000000000)
  total := (-9889688813/500000000000000)
  k := 31
  n := 32
  sFloor := (1099511626505/2199023255552)
  nFloor := (1937182410385/1180591620717411303424)
  eFloor := (281400472945/295147905179352825856)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=650171,width:=130034,den:=68719476736,localDen:=14167099448608935641088,lowerC:=9786303283908,s:=[14167099437234788499456,-4545149140992,-457414017024],L:=[9786303283911,3914515290689,391450926238,-272,32],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor250Source.source.poly i) 650171 130034 68719476736
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor250Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 2) (CoreQuotient.fused G u 0 2) (((15/8) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (15/8) 0 2 WideAnchor250Source.data
    WideAnchor250Source.path_checked WideAnchor250Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor250Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 0) (CoreQuotient.fused G u 2 0) (((15/8) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (15/8) 2 0 WideAnchor250Source.data
    WideAnchor250Source.path_swapped WideAnchor250Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor250Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor250Cell043
