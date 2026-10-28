/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor272Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor272Cell119
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1291879/131072)
  b := (775127/65536)
  s := [(2279808002043/4503599627370496),(-2566593350805/9007199254740992),(335241410117/4503599627370496)]
  L := [(601516492618718747365/590295810358705651712),(-31614663529/4398046511104),(4406627791/2199023255552),(-126745347/274877906944),(9382721/137438953472)]
  c := (1114279505551/1099511627776)
  R := (667095310701/100000000000000)
  total := (1953153300301/125000000000000)
  k := 0
  n := 32
  sFloor := (1331752736757/9007199254740992)
  nFloor := 127300315410364531709902489587928717980196422173492422818549836887638653720132843135262329963626297819136
  eFloor := 124799234854210288289523582462010591958923349511226007999263358012948785579476544159804932187891429277696
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1291879,width:=258375,den:=131072,localDen:=590295810358705651712,lowerC:=598224254368074432512,s:=[298818994443780096,-168204261838356480,43940762106855424],L:=[601516492618718747365,-4243248310346842112,1182895140499357696,-272183560142585856,40298479842492416],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor272Source.source.poly i) 1291879 258375 131072
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor272Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 48) (CoreQuotient.fused G u 0 48) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 48 WideAnchor272Source.data
    WideAnchor272Source.path_checked WideAnchor272Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor272Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 48 0) (CoreQuotient.fused G u 48 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 48 0 WideAnchor272Source.data
    WideAnchor272Source.path_swapped WideAnchor272Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor272Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor272Cell119
