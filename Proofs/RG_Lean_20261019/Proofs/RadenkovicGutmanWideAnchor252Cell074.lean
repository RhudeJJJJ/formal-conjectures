/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor252Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor252Cell074
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1446879/536870912)
  b := (868127/268435456)
  s := [(67926768593/68719476736),(-9899237863/2199023255552),(-107373157/274877906944)]
  L := [(7782853409828738320747/1208925819614629174706176),(710654885193/281474976710656),(32756617885/140737488355328),(-133404885/35184372088832),(-304277/2199023255552)]
  c := (906043384437/140737488355328)
  R := (-63069555734781/25000000000000)
  total := (-1310373274339/1000000000000000)
  k := 8
  n := 32
  sFloor := (2162898371857/4398046511104)
  nFloor := (1193858616725/2251799813685248)
  eFloor := (1075794491489/2251799813685248)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1446879,width:=289375,den:=536870912,localDen:=1208925819614629174706176,lowerC:=7782853409828140744704,s:=[1194980350484049651826688,-5442163568244470841344,-472232138530072035328],L:=[7782853409828738320747,3052239490646569648128,281377205087287377920,-4583756945613127680,-167278049782398976],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor252Source.source.poly i) 1446879 289375 536870912
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
end Gebendorfer.RadenkovicGutman.WideAnchor252Cell074
