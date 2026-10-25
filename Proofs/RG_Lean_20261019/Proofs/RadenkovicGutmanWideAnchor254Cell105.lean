/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor254Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor254Cell105
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1609927/2097152)
  b := (241489/262144)
  s := [(6363075735325/35184372088832),(-1524003734437/35184372088832),(94555078681/17592186044416)]
  L := [(167197839623490430067/147573952589676412928),(256383924433/3298534883328),(-30618536153/1649267441664),(407178173/206158430208),(-9373537/103079215104)]
  c := (622860489873/549755813888)
  R := (6242417801559/100000000000000)
  total := (11789439856861/1000000000000000)
  k := 0
  n := 32
  sFloor := (628522769781/8796093022208)
  nFloor := (580348784039/2)
  eFloor := (710668838091/4)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1609927,width:=321985,den:=2097152,localDen:=442721857769029238784,lowerC:=501593518870326411264,s:=[80066022026929766400,-19176404878092140544,2379556468392198144],L:=[501593518870471290201,34411267833120948224,-8219100714283040768,874408468340015104,-40259034862845952],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor254Source.source.poly i) 1609927 321985 2097152
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor254Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 31) (CoreQuotient.fused G u 0 31) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 31 WideAnchor254Source.data
    WideAnchor254Source.path_checked WideAnchor254Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor254Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 31 0) (CoreQuotient.fused G u 31 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 31 0 WideAnchor254Source.data
    WideAnchor254Source.path_swapped WideAnchor254Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor254Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor254Cell105
