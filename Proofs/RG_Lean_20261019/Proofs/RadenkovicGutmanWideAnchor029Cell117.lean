/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor029Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor029Cell117
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (897139/131072)
  b := (538283/65536)
  s := [(6462779429359/4503599627370496),(-3527817521055/4503599627370496),(449035534929/2251799813685248)]
  L := [(611909045811655839991/590295810358705651712),(-28482678423/2199023255552),(10884738217/3298534883328),(-93807929/137438953472),(18939575/206158430208)]
  c := (1128506870447/1099511627776)
  R := (1301464945541/100000000000000)
  total := (10475062143889/500000000000000)
  k := 0
  n := 32
  sFloor := (1916516489081/4503599627370496)
  nFloor := 264465862989258506967908666816003419869622461562582502128991949855311797208727662100480
  eFloor := 254393481243478509546439687698711335863678017799510480743951758512851381115129906069504
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=897139,width:=179427,den:=131072,localDen:=1770887431076116955136,lowerC:=1817587538205440212992,s:=[2541268276094828544,-1387194294359162880,353135913805283328],L:=[1835727137434967519973,-22937282311738097664,5843699333442043904,-1208705961481469952,162689710450278400],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor029Source.source.poly i) 897139 179427 131072
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor029Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 38) (CoreQuotient.fused G u 9 38) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 38 WideAnchor029Source.data
    WideAnchor029Source.path_checked WideAnchor029Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor029Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 38 9) (CoreQuotient.fused G u 38 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 38 9 WideAnchor029Source.data
    WideAnchor029Source.path_swapped WideAnchor029Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor029Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor029Cell117
