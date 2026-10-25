/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor249Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor249Cell094
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (433355/4194304)
  b := (260013/2097152)
  s := [(2007204892745/2199023255552),(-69178828783/2199023255552),(-217725877/137438953472)]
  L := [(391827517310578478211/4722366482869645213696),(3280957816453/105553116266496),(122855313163/52776558133248),(-221808685/1649267441664),(-2761657/3298534883328)]
  c := (1459671248907/17592186044416)
  R := (-124462179516267/100000000000000)
  total := (-23918753379751/1000000000000000)
  k := 4
  n := 32
  sFloor := (967271224965/2199023255552)
  nFloor := (123488823021/549755813888)
  eFloor := (1085949764121/8796093022208)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=433355,width:=86671,den:=4194304,localDen:=14167099448608935641088,lowerC:=1175482551931320139776,s:=[12931319056066444001280,-445681210797852721152,-22443012508990046208],L:=[1175482551931735434633,440362703788162678784,32978722010932707328,-1905322096087531520,-11861226497769472],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor249Source.source.poly i) 433355 86671 4194304
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor249Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 2) (CoreQuotient.fused G u 0 2) (((36/19) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (36/19) 0 2 WideAnchor249Source.data
    WideAnchor249Source.path_checked WideAnchor249Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor249Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 0) (CoreQuotient.fused G u 2 0) (((36/19) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (36/19) 2 0 WideAnchor249Source.data
    WideAnchor249Source.path_swapped WideAnchor249Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor249Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor249Cell094
