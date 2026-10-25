/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor377Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor377Cell081
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (162013/16777216)
  b := (388831/33554432)
  s := [(1085076928643/1099511627776),(-2798266097/549755813888),(-7302109/17179869184)]
  L := [(2376524713973510989571/604462909807314587353088),(5207776221589/3377699720527872),(240181557049/1688849860263936),(-476984749/211106232532992),(-7365265/105553116266496)]
  c := (1106655557627/281474976710656)
  R := (-276935054751389/100000000000000)
  total := (-646437214347/125000000000000)
  k := 8
  n := 32
  sFloor := (1079013061473/2199023255552)
  nFloor := (146488172077/70368744177664)
  eFloor := (246188613535/70368744177664)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=324026,width:=64805,den:=33554432,localDen:=1813388729421943762059264,lowerC:=7129574141916912549888,s:=[1789582050111671293181952,-9230178333788592930816,-770760360267626840064],L:=[7129574141920532968713,2795903569576400519168,257892983156953317376,-4097267795291537408,-126534289205493760],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor377Source.source.poly i) 324026 64805 33554432
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor377Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 14) (CoreQuotient.fused G u 2 14) (((40/21) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (40/21) 2 14 WideAnchor377Source.data
    WideAnchor377Source.path_checked WideAnchor377Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor377Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 14 2) (CoreQuotient.fused G u 14 2) (((40/21) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (40/21) 14 2 WideAnchor377Source.data
    WideAnchor377Source.path_swapped WideAnchor377Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor377Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor377Cell081
