/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor018Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor018Cell120
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (775127/65536)
  b := (116269/8192)
  s := [(5289986496153/18014398509481984),(-1490938086469/9007199254740992),(24370976507/562949953421312)]
  L := [(299084318070382000309/295147905179352825856),(-66976749883/13194139533312),(9404907757/6597069766656),(-272557121/824633720832),(20293667/412316860416)]
  c := (554926352141/549755813888)
  R := (468060060233/100000000000000)
  total := (13174008235539/1000000000000000)
  k := 0
  n := 32
  sFloor := (1543990785719/18014398509481984)
  nFloor := 238799615434399055077022323458321750760218128499963103256708843095155894995744427343872
  eFloor := 235518271670298046314643479581117397567833048048454855328511186952997734314746769833984
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=775127,width:=155025,den:=65536,localDen:=885443715538058477568,lowerC:=893771450300315467776,s:=[260013416258912256,-146565177652248576,38332231592706048],L:=[897252954211146000927,-4494733599060262912,1262305351194116096,-292655980246728704,43580318040457216],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor018Source.source.poly i) 775127 155025 65536
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor018Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 27) (CoreQuotient.fused G u 9 27) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 27 WideAnchor018Source.data
    WideAnchor018Source.path_checked WideAnchor018Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor018Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 27 9) (CoreQuotient.fused G u 27 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 27 9 WideAnchor018Source.data
    WideAnchor018Source.path_swapped WideAnchor018Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor018Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor018Cell120
