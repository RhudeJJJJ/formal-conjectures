/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor023Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor023Cell083
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (466597/33554432)
  b := (139979/8388608)
  s := [(197882159521/549755813888),(-53385073141/1099511627776),(16888308307/2199023255552)]
  L := [(603358113842904729739/1180591620717411303424),(1551780723701/26388279066624),(-118987043075/13194139533312),(1701773803/1649267441664),(-66238405/824633720832)]
  c := (561921031999/1099511627776)
  R := (-33563002894391/100000000000000)
  total := (-863289369933/1000000000000000)
  k := 1
  n := 32
  sFloor := (701646800109/4398046511104)
  nFloor := (1405841646509/70368744177664)
  eFloor := (647330895747/35184372088832)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=466597,width:=93319,den:=33554432,localDen:=3541774862152233910272,lowerC:=1810074341527705878528,s:=[1274846105406825037824,-171965357426372247552,27200524448748797952],L:=[1810074341528714189217,208276483089343971328,-31940341165929267200,3654531414537273344,-284491783214202880],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor023Source.source.poly i) 466597 93319 33554432
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor023Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 32) (CoreQuotient.fused G u 9 32) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 32 WideAnchor023Source.data
    WideAnchor023Source.path_checked WideAnchor023Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor023Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 32 9) (CoreQuotient.fused G u 32 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 32 9 WideAnchor023Source.data
    WideAnchor023Source.path_swapped WideAnchor023Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor023Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor023Cell083
