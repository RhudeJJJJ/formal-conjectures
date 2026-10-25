/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor255Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor255Cell119
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1291879/131072)
  b := (775127/65536)
  s := [(2279808002043/4503599627370496),(-2566593350803/9007199254740992),(83810352529/1125899906842624)]
  L := [(300758246127891388355/295147905179352825856),(-31614663529/4398046511104),(4406627791/2199023255552),(-126745347/274877906944),(9382721/137438953472)]
  c := (1114279504875/1099511627776)
  R := (41693455023/6250000000000)
  total := (15625225805951/1000000000000000)
  k := 0
  n := 32
  sFloor := (1331752736757/9007199254740992)
  nFloor := 1462348715953619943251148426383499135966513093892812777735357668570169344
  eFloor := 1433617821390968104141973459837227750961437050806935019846000680672165888
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1291879,width:=258375,den:=131072,localDen:=295147905179352825856,lowerC:=299112127002574848000,s:=[149409497221890048,-84102130919112704,21970381053362176],L:=[300758246127891388355,-2121624155173421056,591447570249678848,-136091780071292928,20149239921246208],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor255Source.source.poly i) 1291879 258375 131072
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor255Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 32) (CoreQuotient.fused G u 0 32) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 32 WideAnchor255Source.data
    WideAnchor255Source.path_checked WideAnchor255Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor255Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 32 0) (CoreQuotient.fused G u 32 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 32 0 WideAnchor255Source.data
    WideAnchor255Source.path_swapped WideAnchor255Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor255Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor255Cell119
