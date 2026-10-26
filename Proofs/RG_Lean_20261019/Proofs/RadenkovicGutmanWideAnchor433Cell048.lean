/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor433Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor433Cell048
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (202229/8589934592)
  b := (970699/34359738368)
  s := [(2199023187389/2199023255552),(-13633/1099511627776),(-1363/1099511627776)]
  L := [(4230557628303/590295810358705651712),(5076662765101/1770887431076116955136),(253832801801/885443715538058477568),(-553/110680464442257309696),(-17/55340232221128654848)]
  c := (2115278814151/295147905179352825856)
  R := (-937690026565809/100000000000000)
  total := (-2731865161/62500000000000)
  k := 28
  n := 32
  sFloor := (2199023157397/4398046511104)
  nFloor := (956284608275/147573952589676412928)
  eFloor := (1033993988401/73786976294838206464)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=808916,width:=161783,den:=34359738368,localDen:=1770887431076116955136,lowerC:=12691672884906,s:=[1770887376184018993152,-21957483429888,-2195265159168],L:=[12691672884909,5076662765101,507665603602,-8848,-544],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor433Source.source.poly i) 808916 161783 34359738368
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor433Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 8) (CoreQuotient.fused G u 2 8) (((13/7) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (13/7) 2 8 WideAnchor433Source.data
    WideAnchor433Source.path_checked WideAnchor433Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor433Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 8 2) (CoreQuotient.fused G u 8 2) (((13/7) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (13/7) 8 2 WideAnchor433Source.data
    WideAnchor433Source.path_swapped WideAnchor433Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor433Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor433Cell048
