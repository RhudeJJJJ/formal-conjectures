/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor019Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor019Cell011
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (60867/2199023255552)
  b := (584323/17592186044416)
  s := [(68719476735/68719476736),(-3/549755813888),(-1/1099511627776)]
  L := [(4636176208269/604462909807314587353088),(5563400024509/1813388729421943762059264),(92723143297/302231454903657293676544),(11/113336795588871485128704),(-1/18889465931478580854784)]
  c := (1159044052067/151115727451828646838272)
  R := (-1279685810743301/100000000000000)
  total := (-17580523/250000000000000)
  k := 37
  n := 32
  sFloor := (1099511627753/2199023255552)
  nFloor := (1287882092111/19342813113834066795298816)
  eFloor := (603392937001/9671406556917033397649408)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=486936,width:=97387,den:=17592186044416,localDen:=1813388729421943762059264,lowerC:=13908528624804,s:=[1813388729395555482992640,-9895604649984,-1649267441664],L:=[13908528624807,5563400024509,556338859782,176,-96],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor019Source.source.poly i) 486936 97387 17592186044416
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor019Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 28) (CoreQuotient.fused G u 9 28) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 28 WideAnchor019Source.data
    WideAnchor019Source.path_checked WideAnchor019Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor019Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 28 9) (CoreQuotient.fused G u 28 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 28 9 WideAnchor019Source.data
    WideAnchor019Source.path_swapped WideAnchor019Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor019Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor019Cell011
