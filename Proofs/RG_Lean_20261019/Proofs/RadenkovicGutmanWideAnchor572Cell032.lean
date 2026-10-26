/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor572Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor572Cell032
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (700045/549755813888)
  b := (420027/274877906944)
  s := [(4398046510633/4398046511104),(-189/4398046511104),(-9/2199023255552)]
  L := [(844088669877667069184834147/42535295865117307932921825928971026432),(1199522145545/151115727451828646838272),(59976107269/75557863725914323419136),(5/9444732965739290427392),(-1/4722366482869645213696)]
  c := (1499402681797/75557863725914323419136)
  R := (-1232154889498099/100000000000000)
  total := (-1557058887/500000000000000)
  k := 36
  n := 32
  sFloor := (2199023255213/4398046511104)
  nFloor := (26504421087/1180591620717411303424)
  eFloor := (1143459585845/18889465931478580854784)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=700045,width:=140009,den:=549755813888,localDen:=42535295865117307932921825928971026432,lowerC:=844088669877411448214257664,s:=[42535295860562075444613903198678155264,-1827895839257319312155738112,-174085318024506601157689344],L:=[844088669877667069184834147,337635467981194991784427520,33763546793475162062716928,22517998136852480,-9007199254740992],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor572Source.source.poly i) 700045 140009 549755813888
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor572Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 6 10) (CoreQuotient.fused G u 6 10) (((21/11) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (21/11) 6 10 WideAnchor572Source.data
    WideAnchor572Source.path_checked WideAnchor572Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor572Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 10 6) (CoreQuotient.fused G u 10 6) (((21/11) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (21/11) 10 6 WideAnchor572Source.data
    WideAnchor572Source.path_swapped WideAnchor572Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor572Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor572Cell032
