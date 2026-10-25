/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor261Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor261Cell131
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1439809/16384)
  b := (863885/8192)
  s := [(3396267021293/4611686018427387904),(-486774782885/1152921504606846976),(64563305711/576460752303423488)]
  L := [(18894328324589435475593/18889465931478580854784),(-225638803/2199023255552),(33492085/1099511627776),(-257115/34359738368),(80133/68719476736)]
  c := (274927095859/274877906944)
  R := (8946611049/100000000000000)
  total := (377177985311/200000000000000)
  k := 0
  n := 32
  sFloor := (1965674335441/9223372036854775808)
  nFloor := 39091948024813726614530606596352331692522215385305795473136093535351957186602559370520105220042903350985442897968188262281818005403312922686081683256081102724399104
  eFloor := 39081830237625324514860202176059889208481685582959496861734209756189798031967029752406795244802439404238383742158839377958158224004397017225339446264915959694229504
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1439809,width:=287961,den:=16384,localDen:=18889465931478580854784,lowerC:=18892846167978592436224,s:=[13911109719216128,-7975318042787840,2115610401538048],L:=[18894328324589435475593,-1938222559187173376,575389638999408640,-141350466087813120,22026791317143552],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor261Source.source.poly i) 1439809 287961 16384
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor261Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 38) (CoreQuotient.fused G u 0 38) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 38 WideAnchor261Source.data
    WideAnchor261Source.path_checked WideAnchor261Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor261Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 38 0) (CoreQuotient.fused G u 38 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 38 0 WideAnchor261Source.data
    WideAnchor261Source.path_swapped WideAnchor261Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor261Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor261Cell131
