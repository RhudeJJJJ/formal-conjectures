/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor526Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor526Cell081
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (162013/16777216)
  b := (388831/33554432)
  s := [(4383390024371/4398046511104),(-5835877447/4398046511104),(-284461667/2199023255552)]
  L := [(21343828500547690594359/38685626227668133590597632),(997875210079/4503599627370496),(152055472445/6755399441055744),(9798217/140737488355328),(1367125/422212465065984)]
  c := (1242374331955/2251799813685248)
  R := (-375123038001943/100000000000000)
  total := (-88288222523/12500000000000)
  k := 11
  n := 32
  sFloor := (2188492611795/4398046511104)
  nFloor := (110033891735/140737488355328)
  eFloor := (665729941815/281474976710656)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=324026,width:=64805,den:=33554432,localDen:=116056878683004400771792896,lowerC:=64031485501638872924160,s:=[115670119220957724492693504,-153998762670053212028928,-15012907705106134204416],L:=[64031485501643071783077,25715048356670607458304,2612293125316416634880,8079940142229356544,375792458530816000],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor526Source.source.poly i) 324026 64805 33554432
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor526Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 6) (CoreQuotient.fused G u 4 6) (((13/7) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (13/7) 4 6 WideAnchor526Source.data
    WideAnchor526Source.path_checked WideAnchor526Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor526Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 6 4) (CoreQuotient.fused G u 6 4) (((13/7) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (13/7) 6 4 WideAnchor526Source.data
    WideAnchor526Source.path_swapped WideAnchor526Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor526Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor526Cell081
