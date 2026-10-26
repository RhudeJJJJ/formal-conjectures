/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor033Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor033Cell015
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (504855/8796093022208)
  b := (302913/4398046511104)
  s := [(2199023255551/2199023255552)]
  L := [(4009100752243/38685626227668133590597632),(1202730225667/29014219670751100192948224),(60136511303/14507109835375550096474112),(-1/453347182355485940514816),(1/906694364710971881029632)]
  c := (2004550376121/19342813113834066795298816)
  R := (-747448056670191/50000000000000)
  total := (-34104853/200000000000000)
  k := 44
  n := 32
  sFloor := (2199023255551/4398046511104)
  nFloor := (577805065209/4835703278458516698824704)
  eFloor := (799571414823/4835703278458516698824704)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=504855,width:=100971,den:=8796093022208,localDen:=116056878683004400771792896,lowerC:=12027302256726,s:=[116056878682951624213659648],L:=[12027302256729,4810920902668,481092090424,-256,128],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor033Source.source.poly i) 504855 100971 8796093022208
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor033Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 10 12) (CoreQuotient.fused G u 10 12) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 10 12 WideAnchor033Source.data
    WideAnchor033Source.path_checked WideAnchor033Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor033Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 12 10) (CoreQuotient.fused G u 12 10) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 12 10 WideAnchor033Source.data
    WideAnchor033Source.path_swapped WideAnchor033Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor033Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor033Cell015
