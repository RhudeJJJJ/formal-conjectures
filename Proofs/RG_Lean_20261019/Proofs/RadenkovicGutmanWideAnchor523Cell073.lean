/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor523Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor523Cell073
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1205733/536870912)
  b := (1446879/536870912)
  s := [(4397338494077/4398046511104),(-141575413/2199023255552),(-1767771/274877906944)]
  L := [(14251109397846886346630467/316912650057057350374175801344),(3888613727573/216172782113783808),(194476354385/108086391056891904),(1152943/13510798882111488),(28663/6755399441055744)]
  c := (810081780733/18014398509481984)
  R := (-250238667671319/50000000000000)
  total := (-1102943356431/500000000000000)
  k := 15
  n := 32
  sFloor := (2198513529457/4398046511104)
  nFloor := (20288790351/281474976710656)
  eFloor := (581106703693/4503599627370496)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1205733,width:=241146,den:=536870912,localDen:=950737950171172051122527404032,lowerC:=42753328193540234133110784,s:=[950584896160661531135066505216,-61209501814235911220625408,-6114303603361051456831488],L:=[42753328193540659039891401,17102304037583552975470592,1710632103790348683182080,81131151018428465152,4033958628728766464],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor523Source.source.poly i) 1205733 241146 536870912
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor523Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 6) (CoreQuotient.fused G u 4 6) (((17/9) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (17/9) 4 6 WideAnchor523Source.data
    WideAnchor523Source.path_checked WideAnchor523Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor523Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 6 4) (CoreQuotient.fused G u 6 4) (((17/9) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (17/9) 6 4 WideAnchor523Source.data
    WideAnchor523Source.path_swapped WideAnchor523Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor523Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor523Cell073
