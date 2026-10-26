/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor420Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor420Cell090
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1671897/33554432)
  b := (501569/8388608)
  s := [(4208418285179/4398046511104),(-36064849521/2199023255552),(-1334418313/1099511627776)]
  L := [(1602244616641687205081/75557863725914323419136),(1178344669393/140737488355328),(167508684293/211106232532992),(-76856619/8796093022208),(-5544401/13194139533312)]
  c := (746103290767/35184372088832)
  R := (-192674661907941/100000000000000)
  total := (-9140037042053/500000000000000)
  k := 6
  n := 32
  sFloor := (1032737728221/2199023255552)
  nFloor := (395170274491/8796093022208)
  eFloor := (410594665921/8796093022208)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1671897,width:=334379,den:=33554432,localDen:=226673591177742970257408,lowerC:=4806733849923365634048,s:=[216900226832786478071808,-3717536381468550365184,-275101584648887599104],L:=[4806733849925061615243,1897856931922075189248,179861080208605970432,-1980579990516793344,-95252083883638784],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor420Source.source.poly i) 1671897 334379 33554432
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor420Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 4) (CoreQuotient.fused G u 2 4) (((32/17) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (32/17) 2 4 WideAnchor420Source.data
    WideAnchor420Source.path_checked WideAnchor420Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor420Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 2) (CoreQuotient.fused G u 4 2) (((32/17) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (32/17) 4 2 WideAnchor420Source.data
    WideAnchor420Source.path_swapped WideAnchor420Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor420Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor420Cell090
