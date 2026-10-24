/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanSymbolicAnchor005Source
namespace Gebendorfer.RadenkovicGutman.SymbolicAnchor005Cell141
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (343015/134217728)
  b := (754633/268435456)
  s := [(8126805133043/8796093022208),(-59058270605/4398046511104),(-354563879/1099511627776)]
  L := [(12491922201866090220641/302231454903657293676544),(1599536919085/211106232532992),(26875453211/105553116266496),(-132043987/13194139533312),(152281/6597069766656)]
  c := (1454251143367/35184372088832)
  R := (-159305545961803/100000000000000)
  total := (-6185189489/15625000000000)
  k := 5
  n := 32
  sFloor := (250182877525/549755813888)
  nFloor := (413994069909/1125899906842624)
  eFloor := (396134563053/1125899906842624)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=686030,width:=68603,den:=268435456,localDen:=906694364710971881029632,lowerC:=37475766605591233953792,s:=[837704694417230735081472,-12175360358726070435840,-292385330812397027328],L:=[37475766605598270661923,6869958756214673244160,230858385212846374912,-9073993692775186432,20929341273669632],transformed:=fun i => IntegerPolynomialPaymentCell.affine (SymbolicAnchor005Source.source.poly i) 686030 68603 268435456
}
theorem checked : IntegerPolynomialPaymentCell.checks SymbolicAnchor005Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 14) (CoreQuotient.fused G u 9 14) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 14 SymbolicAnchor005Source.data
    SymbolicAnchor005Source.path_checked SymbolicAnchor005Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry SymbolicAnchor005Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 14 9) (CoreQuotient.fused G u 14 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 14 9 SymbolicAnchor005Source.data
    SymbolicAnchor005Source.path_swapped SymbolicAnchor005Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry SymbolicAnchor005Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.SymbolicAnchor005Cell141
