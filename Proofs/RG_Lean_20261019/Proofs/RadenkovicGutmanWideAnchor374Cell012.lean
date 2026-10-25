/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor374Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor374Cell012
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (584323/17592186044416)
  b := (1402375/35184372088832)
  s := [(4398046511103/4398046511104)]
  L := [(638596111719162041452674247/21778071482940061661655974875633165533184),(5444993279999/464227514732017603087171584),(90749810321/77371252455336267181195264),(13/29014219670751100192948224),(-1/4835703278458516698824704)]
  c := (567187285333/19342813113834066795298816)
  R := (-1558020388583603/100000000000000)
  total := (-51438143/500000000000000)
  k := 45
  n := 32
  sFloor := (2199023255551/4398046511104)
  nFloor := (236840280589/9671406556917033397649408)
  eFloor := (1428871510931/38685626227668133590597632)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1168646,width:=233729,den:=35184372088832,localDen:=65334214448820184984967924626899496599552,lowerC:=1915788335156236493443301376,s:=[65334214448805329704496500063600707108864],L:=[1915788335157486124358022741,766314678338698474707484672,76631402239799773498441728,29273397577908224,-13510798882111488],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor374Source.source.poly i) 1168646 233729 35184372088832
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor374Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 12) (CoreQuotient.fused G u 2 12) (((21/11) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (21/11) 2 12 WideAnchor374Source.data
    WideAnchor374Source.path_checked WideAnchor374Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor374Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 12 2) (CoreQuotient.fused G u 12 2) (((21/11) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (21/11) 12 2 WideAnchor374Source.data
    WideAnchor374Source.path_swapped WideAnchor374Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor374Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor374Cell012
