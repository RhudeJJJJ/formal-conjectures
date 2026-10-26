/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor425Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor425Cell076
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (130219/33554432)
  b := (625051/134217728)
  s := [(4396317340813/4398046511104),(-172828537/1099511627776),(-17233929/1099511627776)]
  L := [(745645000669/4503599627370496),(1789310499821/27021597764222976),(89418547975/13510798882111488),(-1169771/1688849860263936),(-29179/844424930131968)]
  c := (745645000669/4503599627370496)
  R := (-435306896782307/100000000000000)
  total := (-165297774233/50000000000000)
  k := 13
  n := 32
  sFloor := (1098889272737/2199023255552)
  nFloor := (625445398743/2251799813685248)
  eFloor := (742763238731/2251799813685248)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=520876,width:=104175,den:=134217728,localDen:=27021597764222976,lowerC:=4473870004014,s:=[27010973741955072,-4247434125312,-423541039104],L:=[4473870004014,1789310499821,178837095950,-18716336,-933728],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor425Source.source.poly i) 520876 104175 134217728
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor425Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 6) (CoreQuotient.fused G u 2 6) (((36/19) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (36/19) 2 6 WideAnchor425Source.data
    WideAnchor425Source.path_checked WideAnchor425Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor425Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 6 2) (CoreQuotient.fused G u 6 2) (((36/19) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (36/19) 6 2 WideAnchor425Source.data
    WideAnchor425Source.path_swapped WideAnchor425Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor425Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor425Cell076
