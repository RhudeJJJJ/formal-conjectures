/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor539Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor539Cell010
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1623121/70368744177664)
  b := (60867/2199023255552)
  s := [(549755813861/549755813888),(-89/4398046511104),(-3/2199023255552)]
  L := [(604035047857/18889465931478580854784),(1449678755905/113336795588871485128704),(144967339697/113336795588871485128704),(-5/14167099448608935641088),(1/7083549724304467820544)]
  c := (604035047857/18889465931478580854784)
  R := (-302074916274811/25000000000000)
  total := (-55308519/1000000000000000)
  k := 35
  n := 32
  sFloor := (549755813849/1099511627776)
  nFloor := (1345687676857/38685626227668133590597632)
  eFloor := (2066168508261/77371252455336267181195264)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1623121,width:=324623,den:=70368744177664,localDen:=113336795588871485128704,lowerC:=3624210287142,s:=[113336795583305207513088,-2293512536064,-154618822656],L:=[3624210287142,1449678755905,144967339697,-40,16],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor539Source.source.poly i) 1623121 324623 70368744177664
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor539Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 5 17) (CoreQuotient.fused G u 5 17) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 5 17 WideAnchor539Source.data
    WideAnchor539Source.path_checked WideAnchor539Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor539Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 17 5) (CoreQuotient.fused G u 17 5) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 17 5 WideAnchor539Source.data
    WideAnchor539Source.path_swapped WideAnchor539Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor539Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor539Cell010
