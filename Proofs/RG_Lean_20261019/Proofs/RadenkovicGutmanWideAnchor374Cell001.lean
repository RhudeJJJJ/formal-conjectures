/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor374Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor374Cell001
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1258291/281474976710656)
  b := (1509949/281474976710656)
  s := [(4398046511103/4398046511104)]
  L := [(1480650277310277445135539349/2787593149816327892691964784081045188247552),(3156193387919/14855280471424563298789490688),(157809543977/7427640235712281649394745344),(-1/464227514732017603087171584),(1/464227514732017603087171584)]
  c := (1315081623429/2475880078570760549798248448)
  R := (-1758573679013721/100000000000000)
  total := (-977441/62500000000000)
  k := 51
  n := 32
  sFloor := (2199023255551/4398046511104)
  nFloor := (549138368833/1237940039285380274899124224)
  eFloor := (51765382299/77371252455336267181195264)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1258291,width:=251658,den:=281474976710656,localDen:=8362779449448983678075894352243135564742656,lowerC:=4441950831927473506602713088,s:=[8362779449447082202175552008140890509934592],L:=[4441950831930832335406618047,1776778920717653966457929728,177677750862581275346075648,-18014398509481984,18014398509481984],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor374Source.source.poly i) 1258291 251658 281474976710656
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
end Gebendorfer.RadenkovicGutman.WideAnchor374Cell001
