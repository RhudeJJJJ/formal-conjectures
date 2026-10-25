/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor012Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor012Cell057
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (521727/4294967296)
  b := (78259/536870912)
  s := [(1098647387875/1099511627776),(-690594855/2199023255552),(-17154813/549755813888)]
  L := [(2841656960901718646690781/4951760157141521099596496896),(6197695717193/27021597764222976),(102960658817/4503599627370496),(-24994193/1688849860263936),(-205521/281474976710656)]
  c := (646117987549/1125899906842624)
  R := (-9328888825851/2500000000000)
  total := (-44190973147/500000000000000)
  k := 11
  n := 32
  sFloor := (2196535561643/4398046511104)
  nFloor := (816579983223/576460752303423488)
  eFloor := (279725393015/288230376151711744)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=521727,width:=104345,den:=4294967296,localDen:=14855280471424563298789490688,lowerC:=8524970882704251486732288,s:=[14843603899936256355729408000,-4665244097462972574597120,-463550456606463243583488],L:=[8524970882705155940072343,3407219253235609589776384,339619324718307109502976,-219851246643020038144,-10846691004103262208],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor012Source.source.poly i) 521727 104345 4294967296
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor012Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 21) (CoreQuotient.fused G u 9 21) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 21 WideAnchor012Source.data
    WideAnchor012Source.path_checked WideAnchor012Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor012Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 21 9) (CoreQuotient.fused G u 21 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 21 9 WideAnchor012Source.data
    WideAnchor012Source.path_swapped WideAnchor012Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor012Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor012Cell057
