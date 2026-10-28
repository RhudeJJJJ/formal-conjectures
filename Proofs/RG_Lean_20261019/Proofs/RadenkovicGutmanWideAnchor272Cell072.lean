/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor272Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor272Cell072
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (502389/268435456)
  b := (1205733/536870912)
  s := [(544272577179/549755813888),(-17132292235/4398046511104),(-746805673/2199023255552)]
  L := [(5482015347528363840793/1208925819614629174706176),(250359273193/140737488355328),(23109417717/140737488355328),(-11586309/4398046511104),(-854563/8796093022208)]
  c := (1276381161885/281474976710656)
  R := (-269800734721111/100000000000000)
  total := (-975558439961/1000000000000000)
  k := 8
  n := 32
  sFloor := (2167777356925/4398046511104)
  nFloor := (722936783647/2251799813685248)
  eFloor := (1598078561151/4503599627370496)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1004778,width:=200955,den:=536870912,localDen:=1208925819614629174706176,lowerC:=5482015347526556712960,s:=[1196868054575841760247808,-4709288630709743779840,-410560760576290586624],L:=[5482015347528363840793,2150569781228528992256,198508386648235966464,-3184820367126429696,-117450244395892736],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor272Source.source.poly i) 1004778 200955 536870912
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor272Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 48) (CoreQuotient.fused G u 0 48) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 48 WideAnchor272Source.data
    WideAnchor272Source.path_checked WideAnchor272Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor272Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 48 0) (CoreQuotient.fused G u 48 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 48 0 WideAnchor272Source.data
    WideAnchor272Source.path_swapped WideAnchor272Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor272Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor272Cell072
