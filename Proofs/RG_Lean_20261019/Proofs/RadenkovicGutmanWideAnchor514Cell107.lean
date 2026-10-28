/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor514Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor514Cell107
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1159147/1048576)
  b := (10867/8192)
  s := [(1514620576723/17592186044416),(-845509346433/35184372088832),(61152055403/17592186044416)]
  L := [(686829386848037605169/590295810358705651712),(460899076487/13194139533312),(-29378105691/2199023255552),(1676353807/824633720832),(-22730017/137438953472)]
  c := (1279319425761/1099511627776)
  R := (757310657181/10000000000000)
  total := (2251949609807/125000000000000)
  k := 0
  n := 32
  sFloor := (1153017958909/35184372088832)
  nFloor := 922573125385276081831936
  eFloor := 667196557821181786324992
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1159147,width:=231829,den:=1048576,localDen:=1770887431076116955136,lowerC:=2060488160542873092096,s:=[152466699442358059008,-42555878805375811584,6155767454040588288],L:=[2060488160544112815507,61860826883383361536,-23658375592739340288,3599942388795047936,-292874038957572096],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor514Source.source.poly i) 1159147 231829 1048576
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor514Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 44) (CoreQuotient.fused G u 4 44) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 4 44 WideAnchor514Source.data
    WideAnchor514Source.path_checked WideAnchor514Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor514Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 44 4) (CoreQuotient.fused G u 44 4) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 44 4 WideAnchor514Source.data
    WideAnchor514Source.path_swapped WideAnchor514Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor514Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor514Cell107
