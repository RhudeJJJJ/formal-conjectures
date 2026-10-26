/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor533Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor533Cell101
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1552785/4194304)
  b := (931671/2097152)
  s := [(3775413153841/17592186044416),(-117110643043/8796093022208),(-3379250437/2199023255552)]
  L := [(123443739998448726529/147573952589676412928),(312572269655/6597069766656),(11560304557/3298534883328),(-692596223/412316860416),(47608703/206158430208)]
  c := (229931883511/274877906944)
  R := (-8927195895989/100000000000000)
  total := (-2773474165781/500000000000000)
  k := 1
  n := 32
  sFloor := (1757078932129/17592186044416)
  nFloor := (391534148161/536870912)
  eFloor := (1210656944095/2147483648)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1552785,width:=310557,den:=4194304,localDen:=442721857769029238784,lowerC:=370331219995284996096,s:=[95011382956847529984,-5894371662693924864,-680332973995720704],L:=[370331219995346179587,20976369934448721920,1551597812628586496,-743669531779530752,102238911194988544],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor533Source.source.poly i) 1552785 310557 4194304
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor533Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 5 11) (CoreQuotient.fused G u 5 11) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 5 11 WideAnchor533Source.data
    WideAnchor533Source.path_checked WideAnchor533Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor533Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 11 5) (CoreQuotient.fused G u 11 5) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 11 5 WideAnchor533Source.data
    WideAnchor533Source.path_swapped WideAnchor533Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor533Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor533Cell101
