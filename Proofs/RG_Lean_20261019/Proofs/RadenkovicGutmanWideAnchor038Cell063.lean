/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor038Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor038Cell063
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1557865/4294967296)
  b := (934719/2147483648)
  s := [(4395651024153/4398046511104),(-478652257/2199023255552),(-5952321/274877906944)]
  L := [(2846486136138516532076417/9903520314283042199192993792),(3104469063269/27021597764222976),(12899186801/1125899906842624),(-675893/105553116266496),(-44581/140737488355328)]
  c := (80902001859/281474976710656)
  R := (-407728013065741/100000000000000)
  total := (-288986788777/1000000000000000)
  k := 12
  n := 32
  sFloor := (2197299241251/4398046511104)
  nFloor := (308799867835/36028797018963968)
  eFloor := (585342301569/72057594037927936)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1557865,width:=311573,den:=4294967296,localDen:=29710560942849126597578981376,lowerC:=8539458408415302531416064,s:=[29694378471639284869163384832,-6466974378795740656828416,-643364895302149874909184],L:=[8539458408415549596229251,3413399833135132121759744,340387341037300900429824,-190246966433895415808,-9411326952553316352],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor038Source.source.poly i) 1557865 311573 4294967296
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor038Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 10 17) (CoreQuotient.fused G u 10 17) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 10 17 WideAnchor038Source.data
    WideAnchor038Source.path_checked WideAnchor038Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor038Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 17 10) (CoreQuotient.fused G u 17 10) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 17 10 WideAnchor038Source.data
    WideAnchor038Source.path_swapped WideAnchor038Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor038Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor038Cell063
