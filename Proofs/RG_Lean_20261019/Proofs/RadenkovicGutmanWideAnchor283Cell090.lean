/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor283Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor283Cell090
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1671897/33554432)
  b := (501569/8388608)
  s := [(2040911123745/2199023255552),(-55887847385/2199023255552),(-298587675/274877906944)]
  L := [(23761228745868415341/590295810358705651712),(265366319169/17592186044416),(40167194097/35184372088832),(-32818079/549755813888),(756399/2199023255552)]
  c := (177034949853/4398046511104)
  R := (-40157107208661/25000000000000)
  total := (-15138205586181/1000000000000000)
  k := 5
  n := 32
  sFloor := (123914660935/274877906944)
  nFloor := (550389093629/8796093022208)
  eFloor := (2039560857657/35184372088832)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1671897,width:=334379,den:=33554432,localDen:=590295810358705651712,lowerC:=23761228745863593984,s:=[547852908157961502720,-15002279797650882560,-641212149556838400],L:=[23761228745868415341,8904216111646507008,673893691479293952,-35238144005636096,203044310482944],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor283Source.source.poly i) 1671897 334379 33554432
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor283Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 8) (CoreQuotient.fused G u 0 8) (((19/10) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (19/10) 0 8 WideAnchor283Source.data
    WideAnchor283Source.path_checked WideAnchor283Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor283Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 8 0) (CoreQuotient.fused G u 8 0) (((19/10) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (19/10) 8 0 WideAnchor283Source.data
    WideAnchor283Source.path_swapped WideAnchor283Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor283Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor283Cell090
