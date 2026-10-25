/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor252Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor252Cell131
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1439809/16384)
  b := (863885/8192)
  s := [(6792534042587/9223372036854775808),(-3894198263083/9223372036854775808),(516506445689/4611686018427387904)]
  L := [(9447164162204418619337/9444732965739290427392),(-225638803/2199023255552),(33492085/1099511627776),(-257115/34359738368),(80133/68719476736)]
  c := (549854191713/549755813888)
  R := (4473305297/50000000000000)
  total := (377177968499/200000000000000)
  k := 0
  n := 32
  sFloor := (1965674335441/9223372036854775808)
  nFloor := 399158617318465321662252425703733172893997670345365352761525874143512213385669706110869534153745748939554479712368892028823535616
  eFloor := 399055306991276215879972603733471896103317460871625444432514719961244018195528666822179717480070527645602414279017033082926530560
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1439809,width:=287961,den:=16384,localDen:=9444732965739290427392,lowerC:=9446423083903396872192,s:=[6955554859609088,-3987659021396992,1057805200771072],L:=[9447164162204418619337,-969111279593586688,287694819499704320,-70675233043906560,11013395658571776],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor252Source.source.poly i) 1439809 287961 16384
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor252Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 29) (CoreQuotient.fused G u 0 29) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 29 WideAnchor252Source.data
    WideAnchor252Source.path_checked WideAnchor252Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor252Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 29 0) (CoreQuotient.fused G u 29 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 29 0 WideAnchor252Source.data
    WideAnchor252Source.path_swapped WideAnchor252Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor252Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor252Cell131
