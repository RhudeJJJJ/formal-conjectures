/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor504Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor504Cell132
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (863885/8192)
  b := (518331/4096)
  s := [(7861990563425/18446744073709551616),(-2253710804653/9223372036854775808),(37365743601/576460752303423488)]
  L := [(9446422934959972180749/9444732965739290427392),(-313847799/4398046511104),(46608245/2199023255552),(-1431849/274877906944),(111595/137438953472)]
  c := (1099648373623/1099511627776)
  R := (6218094503/100000000000000)
  total := (786512685961/500000000000000)
  k := 0
  n := 32
  sFloor := (1137568187337/9223372036854775808)
  nFloor := 174522916393329487762075009563598370511614024507616037336491569062695690015165317513177413745650813076084287217122974509175739927760682507917307515823757636273123828432896
  eFloor := 174491545306748954425360359470287942255214873679767176566054464470982267019100100391285346206861734576534052595704574910922261871588526051068208861082668609247140716216320
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=863885,width:=172777,den:=8192,localDen:=9444732965739290427392,lowerC:=9445907603620748066816,s:=[4025339168473600,-2307799863964672,612200343158784],L:=[9446422934959972180749,-673983016313290752,200180887998955520,-49197957022482432,7668750006353920],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor504Source.source.poly i) 863885 172777 8192
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor504Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 34) (CoreQuotient.fused G u 4 34) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 4 34 WideAnchor504Source.data
    WideAnchor504Source.path_checked WideAnchor504Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor504Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 34 4) (CoreQuotient.fused G u 34 4) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 34 4 WideAnchor504Source.data
    WideAnchor504Source.path_swapped WideAnchor504Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor504Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor504Cell132
