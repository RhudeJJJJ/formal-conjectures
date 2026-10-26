/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor538Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor538Cell050
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (582419/17179869184)
  b := (1397805/34359738368)
  s := [(68716574797/68719476736),(-37142419/2199023255552),(-1856477/1099511627776)]
  L := [(3143591645405/144115188075855872),(943033873517/108086391056891904),(188573337803/216172782113783808),(-102961/3377699720527872),(-20579/13510798882111488)]
  c := (785897911351/36028797018963968)
  R := (-268325054840859/50000000000000)
  total := (-1117207117/31250000000000)
  k := 16
  n := 32
  sFloor := (2198889538131/4398046511104)
  nFloor := (1092054334711/18446744073709551616)
  eFloor := (528549280111/9223372036854775808)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1164838,width:=232967,den:=34359738368,localDen:=432345564227567616,lowerC:=9430774936212,s:=[432327306806034432,-7302496714752,-729996460032],L:=[9430774936215,3772135494068,377146675606,-13179008,-658528],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor538Source.source.poly i) 1164838 232967 34359738368
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor538Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 5 16) (CoreQuotient.fused G u 5 16) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 5 16 WideAnchor538Source.data
    WideAnchor538Source.path_checked WideAnchor538Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor538Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 16 5) (CoreQuotient.fused G u 16 5) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 16 5 WideAnchor538Source.data
    WideAnchor538Source.path_swapped WideAnchor538Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor538Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor538Cell050
