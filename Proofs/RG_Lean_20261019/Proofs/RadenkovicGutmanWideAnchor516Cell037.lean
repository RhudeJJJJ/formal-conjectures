/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor516Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor516Cell037
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (435483/137438953472)
  b := (1045159/274877906944)
  s := [(1099511627511/1099511627776),(-211/2199023255552),(-11/1099511627776)]
  L := [(326330221867590921727549743/2658455991569831745807614120560689152),(231871302363/4722366482869645213696),(139122621607/28334198897217871282176),(1/1180591620717411303424),(-1/1770887431076116955136)]
  c := (579678921517/4722366482869645213696)
  R := (-1141042839835227/100000000000000)
  total := (-7171508453/1000000000000000)
  k := 33
  n := 32
  sFloor := (2199023254789/4398046511104)
  nFloor := (539780158521/2361183241434822606848)
  eFloor := (529643780775/2361183241434822606848)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=870966,width:=174193,den:=274877906944,localDen:=7975367974709495237422842361682067456,lowerC:=978990665601934573449510912,s:=[7975367972787303184235581973899247616,-765250043816060267589009408,-79789104094565525530607616],L:=[978990665602772765182649229,391595816594969403240480768,39159536676755732212744192,6755399441055744,-4503599627370496],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor516Source.source.poly i) 870966 174193 274877906944
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor516Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 4) (CoreQuotient.fused G u 4 4) (((25/13) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (25/13) 4 4 WideAnchor516Source.data
    WideAnchor516Source.path_checked WideAnchor516Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor516Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 4) (CoreQuotient.fused G u 4 4) (((25/13) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (25/13) 4 4 WideAnchor516Source.data
    WideAnchor516Source.path_swapped WideAnchor516Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor516Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor516Cell037
