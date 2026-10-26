/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor281Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor281Cell086
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1612557/67108864)
  b := (483767/16777216)
  s := [(4802205984025/17592186044416),(-398940603909/17592186044416),(47401133735/8796093022208)]
  L := [(181579621163088305617/295147905179352825856),(850801403077/26388279066624),(-112801987025/13194139533312),(2248345901/1649267441664),(-121975099/824633720832)]
  c := (676436801117/1099511627776)
  R := (-971564725157/4000000000000)
  total := (-222993661233/200000000000000)
  k := 1
  n := 32
  sFloor := (140564613987/1099511627776)
  nFloor := (486646087077/35184372088832)
  eFloor := (225884472721/17592186044416)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1612557,width:=322511,den:=67108864,localDen:=885443715538058477568,lowerC:=544738863489069613056,s:=[241702941211439923200,-20079338048855212032,4771554355901890560],L:=[544738863489264916851,28548157825051787264,-7570013206190489600,1207071514361331712,-130969765282840576],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor281Source.source.poly i) 1612557 322511 67108864
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor281Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 7) (CoreQuotient.fused G u 0 7) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 7 WideAnchor281Source.data
    WideAnchor281Source.path_checked WideAnchor281Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor281Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 7 0) (CoreQuotient.fused G u 7 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 7 0 WideAnchor281Source.data
    WideAnchor281Source.path_swapped WideAnchor281Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor281Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor281Cell086
