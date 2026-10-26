/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor432Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor432Cell071
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (837315/536870912)
  b := (502389/268435456)
  s := [(2198796484357/2199023255552),(-90692705/2199023255552),(-2265129/549755813888)]
  L := [(4616266477331/144115188075855872),(923205886169/72057594037927936),(138452442185/108086391056891904),(-236935/4503599627370496),(-17729/6755399441055744)]
  c := (288516654833/9007199254740992)
  R := (-517439095969581/100000000000000)
  total := (-1584781744561/1000000000000000)
  k := 15
  n := 32
  sFloor := (4294329553/8589934592)
  nFloor := (1388399477791/36028797018963968)
  eFloor := (279379027061/4503599627370496)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=837315,width:=167463,den:=536870912,localDen:=432345564227567616,lowerC:=13848799431984,s:=[432300979196461056,-17830911344640,-1781369929728],L:=[13848799431993,5539235317014,553809768740,-22745760,-1134656],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor432Source.source.poly i) 837315 167463 536870912
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor432Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 8) (CoreQuotient.fused G u 2 8) (((32/17) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (32/17) 2 8 WideAnchor432Source.data
    WideAnchor432Source.path_checked WideAnchor432Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor432Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 8 2) (CoreQuotient.fused G u 8 2) (((32/17) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (32/17) 8 2 WideAnchor432Source.data
    WideAnchor432Source.path_swapped WideAnchor432Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor432Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor432Cell071
