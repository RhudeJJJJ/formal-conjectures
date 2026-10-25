/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor250Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor250Cell010
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1623121/70368744177664)
  b := (60867/2199023255552)
  s := [(4398046511103/4398046511104)]
  L := [(89413653040385298462614843/21778071482940061661655974875633165533184),(31765993397/19342813113834066795298816),(76238102297/464227514732017603087171584),(5/38685626227668133590597632),(-1/14507109835375550096474112)]
  c := (79415277057/19342813113834066795298816)
  R := (-1656320328704209/100000000000000)
  total := (-18994119/250000000000000)
  k := 48
  n := 32
  sFloor := (2199023255551/4398046511104)
  nFloor := (1509131673851/154742504910672534362390528)
  eFloor := (1753765115681/309485009821345068724781056)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1623121,width:=324623,den:=70368744177664,localDen:=65334214448820184984967924626899496599552,lowerC:=268240959121072425170632704,s:=[65334214448805329704496500063600707108864],L:=[268240959121155895387844529,107295987019337127306461184,10729559034256342348988416,8444249301319680,-4503599627370496],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor250Source.source.poly i) 1623121 324623 70368744177664
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
end Gebendorfer.RadenkovicGutman.WideAnchor250Cell010
