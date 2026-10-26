/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor523Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor523Cell075
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (868127/268435456)
  b := (130219/33554432)
  s := [(4396578690963/4398046511104),(-586889117/4398046511104),(-29278491/2199023255552)]
  L := [(29552931462702084469118717/316912650057057350374175801344),(4032221781539/108086391056891904),(201709716317/54043195528445952),(2473393/6755399441055744),(61147/3377699720527872)]
  c := (1679889661699/18014398509481984)
  R := (-116002481507629/25000000000000)
  total := (-117623913433/40000000000000)
  k := 14
  n := 32
  sFloor := (68686456951/137438953472)
  nFloor := (1346775275759/9007199254740992)
  eFloor := (37662546077/140737488355328)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=868127,width:=173625,den:=268435456,localDen:=950737950171172051122527404032,lowerC:=88658794388099589684068352,s:=[950420647407649434695425327104,-126869453214191972606017536,-12658425711126760396947456],L:=[88658794388106253407356151,35467797876590308451418112,3548514856415037721935872,348099118535649787904,17211350400926482432],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor523Source.source.poly i) 868127 173625 268435456
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor523Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 6) (CoreQuotient.fused G u 4 6) (((17/9) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (17/9) 4 6 WideAnchor523Source.data
    WideAnchor523Source.path_checked WideAnchor523Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor523Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 6 4) (CoreQuotient.fused G u 6 4) (((17/9) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (17/9) 6 4 WideAnchor523Source.data
    WideAnchor523Source.path_swapped WideAnchor523Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor523Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor523Cell075
