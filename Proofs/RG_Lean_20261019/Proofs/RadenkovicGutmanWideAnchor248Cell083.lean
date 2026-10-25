/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor248Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor248Cell083
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (466597/33554432)
  b := (139979/8388608)
  s := [(4390133537097/4398046511104),(-789652663/1099511627776),(-78057609/1099511627776)]
  L := [(17029438477026333738731/9671406556917033397649408),(593922826325/844424930131968),(14766052265/211106232532992),(-16341809/211106232532992),(-199889/52776558133248)]
  c := (1982487560835/1125899906842624)
  R := (-317099275602289/100000000000000)
  total := (-8558644606539/1000000000000000)
  k := 10
  n := 32
  sFloor := (548332837001/1099511627776)
  nFloor := (36943914431/8796093022208)
  eFloor := (1209074297333/562949953421312)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=466597,width:=93319,den:=33554432,localDen:=29014219670751100192948224,lowerC:=51088315431078812712960,s:=[28962017229165185709637632,-20837574836946796019712,-2059805969565421142016],L:=[51088315431079001216193,20407032923310102937600,2029430770214455214080,-2246001126799310848,-109890139882258432],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor248Source.source.poly i) 466597 93319 33554432
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor248Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 2) (CoreQuotient.fused G u 0 2) (((48/25) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (48/25) 0 2 WideAnchor248Source.data
    WideAnchor248Source.path_checked WideAnchor248Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor248Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 0) (CoreQuotient.fused G u 2 0) (((48/25) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (48/25) 2 0 WideAnchor248Source.data
    WideAnchor248Source.path_swapped WideAnchor248Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor248Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor248Cell083
