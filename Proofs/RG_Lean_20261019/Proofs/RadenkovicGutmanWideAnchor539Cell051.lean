/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor539Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor539Cell051
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1397805/34359738368)
  b := (838683/17179869184)
  s := [(4397374966955/4398046511104),(-268558201/4398046511104),(-13411413/2199023255552)]
  L := [(31518534175481192371791049/316912650057057350374175801344),(4299224594561/108086391056891904),(214827979345/54043195528445952),(-3330065/6755399441055744),(-83041/3377699720527872)]
  c := (1791621240015/18014398509481984)
  R := (-57598785648091/12500000000000)
  total := (-18364379567/500000000000000)
  k := 14
  n := 32
  sFloor := (549634948241/1099511627776)
  nFloor := (998011931047/9223372036854775808)
  eFloor := (766173647413/9223372036854775808)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1397805,width:=279561,den:=34359738368,localDen:=950737950171172051122527404032,lowerC:=94555602526413515359518720,s:=[950592780604170487754014064640,-58054973469642756779409408,-5798364920573935283601408],L:=[94555602526443577115373147,37816379457123029969010688,3779293780183197700587520,-468664984159985336320,-23373963541029584896],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor539Source.source.poly i) 1397805 279561 34359738368
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor539Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 5 17) (CoreQuotient.fused G u 5 17) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 5 17 WideAnchor539Source.data
    WideAnchor539Source.path_checked WideAnchor539Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor539Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 17 5) (CoreQuotient.fused G u 17 5) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 17 5 WideAnchor539Source.data
    WideAnchor539Source.path_swapped WideAnchor539Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor539Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor539Cell051
