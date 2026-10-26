/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor267Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor267Cell074
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1446879/536870912)
  b := (868127/268435456)
  s := [(2183904630329/2199023255552),(-2973095367/1099511627776),(-33763155/137438953472)]
  L := [(1150497949443112668853/302231454903657293676544),(5071492903991/3377699720527872),(239460722221/1688849860263936),(-343253225/211106232532992),(-6944665/105553116266496)]
  c := (1071484712365/281474976710656)
  R := (-69637478532841/25000000000000)
  total := (-1451659856387/1000000000000000)
  k := 9
  n := 32
  sFloor := (2177418229115/4398046511104)
  nFloor := (105391485269/140737488355328)
  eFloor := (1528013869285/2251799813685248)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1446879,width:=289375,den:=536870912,localDen:=906694364710971881029632,lowerC:=3451493848328731361280,s:=[900460700625218373156864,-2451714694877590585344,-222737889077420359680],L:=[3451493848329338006559,1361368510283588304896,128559496326966935552,-1474261375621529600,-59654218113351680],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor267Source.source.poly i) 1446879 289375 536870912
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor267Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 43) (CoreQuotient.fused G u 0 43) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 43 WideAnchor267Source.data
    WideAnchor267Source.path_checked WideAnchor267Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor267Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 43 0) (CoreQuotient.fused G u 43 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 43 0 WideAnchor267Source.data
    WideAnchor267Source.path_swapped WideAnchor267Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor267Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor267Cell074
