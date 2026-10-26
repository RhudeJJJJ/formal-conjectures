/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor266Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor266Cell086
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1612557/67108864)
  b := (483767/16777216)
  s := [(6561602656175/8796093022208),(-151485305607/4398046511104),(10707588631/2199023255552)]
  L := [(82583139862308266783/590295810358705651712),(640739463215/26388279066624),(-17722060181/6597069766656),(348554233/1649267441664),(2369657/412316860416)]
  c := (615292339491/4398046511104)
  R := (-24585228036767/25000000000000)
  total := (-113538024127/25000000000000)
  k := 3
  n := 32
  sFloor := (1575365599871/4398046511104)
  nFloor := (2125970468449/35184372088832)
  eFloor := (1105497833541/17592186044416)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1612557,width:=322511,den:=67108864,localDen:=1770887431076116955136,lowerC:=247749419586860089344,s:=[1321025100825860505600,-60996040631871602688,8622889310468702208],L:=[247749419586924800349,42999297496328437760,-4757229305946177536,374257257904340992,10177599317737472],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor266Source.source.poly i) 1612557 322511 67108864
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor266Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 42) (CoreQuotient.fused G u 0 42) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 42 WideAnchor266Source.data
    WideAnchor266Source.path_checked WideAnchor266Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor266Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 42 0) (CoreQuotient.fused G u 42 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 42 0 WideAnchor266Source.data
    WideAnchor266Source.path_swapped WideAnchor266Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor266Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor266Cell086
