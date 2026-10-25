/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor253Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor253Cell017
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (726991/8796093022208)
  b := (872389/8796093022208)
  s := [(2199023255547/2199023255552),(-1/1099511627776)]
  L := [(320899557065/302231454903657293676544),(770157877573/1813388729421943762059264),(25671893941/604462909807314587353088),(-1/453347182355485940514816)]
  c := (320899557065/302231454903657293676544)
  R := (-689277151972607/50000000000000)
  total := (-9052937/40000000000000)
  k := 40
  n := 32
  sFloor := (2199023255545/4398046511104)
  nFloor := (264064960943/604462909807314587353088)
  eFloor := (271563932375/604462909807314587353088)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=726991,width:=145398,den:=8796093022208,localDen:=1813388729421943762059264,lowerC:=1925397342390,s:=[1813388729417820593455104,-1649267441664],L:=[1925397342390,770157877573,77015681823,-4],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor253Source.source.poly i) 726991 145398 8796093022208
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor253Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 30) (CoreQuotient.fused G u 0 30) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 30 WideAnchor253Source.data
    WideAnchor253Source.path_checked WideAnchor253Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor253Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 30 0) (CoreQuotient.fused G u 30 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 30 0 WideAnchor253Source.data
    WideAnchor253Source.path_swapped WideAnchor253Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor253Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor253Cell017
