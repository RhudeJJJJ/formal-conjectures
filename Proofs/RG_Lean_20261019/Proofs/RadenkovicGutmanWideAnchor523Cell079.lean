/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor523Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor523Cell079
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (900073/134217728)
  b := (1080087/134217728)
  s := [(274483997535/274877906944),(-2516631289/4398046511104),(-124619509/2199023255552)]
  L := [(993150958807937098742715/2475880078570760549798248448),(4337939391317/27021597764222976),(72450142047/4503599627370496),(11277949/1688849860263936),(89421/281474976710656)]
  c := (1806531070193/4503599627370496)
  R := (-195530595065513/50000000000000)
  total := (-1279789632783/250000000000000)
  k := 12
  n := 32
  sFloor := (1097244522563/2199023255552)
  nFloor := (90701251631/140737488355328)
  eFloor := (162130765767/140737488355328)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=900073,width:=180014,den:=134217728,localDen:=7427640235712281649394745344,lowerC:=2979452876423737116721152,s:=[7416996174106740855574364160,-4250212400763499135893504,-420927280721620629454848],L:=[2979452876423811296228145,1192403700335146327605248,119489660422049086046208,49600944251858845696,2359666302416584704],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor523Source.source.poly i) 900073 180014 134217728
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
end Gebendorfer.RadenkovicGutman.WideAnchor523Cell079
