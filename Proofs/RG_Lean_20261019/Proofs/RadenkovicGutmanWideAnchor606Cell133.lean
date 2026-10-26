/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor606Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor606Cell133
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (518331/4096)
  b := 128
  s := [(1137560868311/4611686018427387904),(-156822213187/18446744073709551616),(1751551997/9223372036854775808)]
  L := [(154761750031876854871026789/154742504910672534362390528),(-37633495/13194139533312),(323567/6597069766656),(-605/824633720832),(1/412316860416)]
  c := (1099645289585/1099511627776)
  R := (379866621/6250000000000)
  total := (89406733583/1000000000000000)
  k := 0
  n := 32
  sFloor := (2198462182025/18446744073709551616)
  nFloor := 37480695851137302328496948762777131613578433427785917021314940403712
  eFloor := 37476016517728455956145353171109661215346846908937323411610053640192
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=518331,width:=5957,den:=4096,localDen:=464227514732017603087171584,lowerC:=464283948413880671812976640,s:=[114510626404807213056,-3946560216354521088,88158498566701056],L:=[464285250095630564613080367,-1324110891083198627840,22769003447334207488,-340584721819893760,1125899906842624],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor606Source.source.poly i) 518331 5957 4096
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
end Gebendorfer.RadenkovicGutman.WideAnchor606Cell133
