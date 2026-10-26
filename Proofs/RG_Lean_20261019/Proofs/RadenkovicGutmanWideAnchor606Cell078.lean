/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor606Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor606Cell078
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (750061/134217728)
  b := (900073/134217728)
  s := [(4392837183201/4398046511104),(-2080859987/4398046511104),(-103248731/2199023255552)]
  L := [(889938081023002304526575/2475880078570760549798248448),(3886533223325/27021597764222976),(194614797937/13510798882111488),(3580415/844424930131968),(170237/844424930131968)]
  c := (202348492399/562949953421312)
  R := (-396547729482943/100000000000000)
  total := (-2163657252623/500000000000000)
  k := 12
  n := 32
  sFloor := (548818728219/1099511627776)
  nFloor := (317401719381/562949953421312)
  eFloor := (1046545816655/1125899906842624)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=750061,width:=150012,den:=134217728,localDen:=7427640235712281649394745344,lowerC:=2669814243067728639295488,s:=[7418842463011231076645339136,-3514260098273765681528832,-348743209843557434130432],L:=[2669814243069006913579725,1068322117695893720268800,106990616634504098349056,31493663398108856320,1497420487821623296],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor606Source.source.poly i) 750061 150012 134217728
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor606Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 6 6) (CoreQuotient.fused G u 6 6) (((44/23) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (44/23) 6 6 WideAnchor606Source.data
    WideAnchor606Source.path_checked WideAnchor606Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor606Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 6 6) (CoreQuotient.fused G u 6 6) (((44/23) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (44/23) 6 6 WideAnchor606Source.data
    WideAnchor606Source.path_swapped WideAnchor606Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor606Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor606Cell078
