/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor040Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor040Cell043
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (650171/68719476736)
  b := (780205/68719476736)
  s := [(4398045164275/4398046511104),(-538733/4398046511104),(-26935/2199023255552)]
  L := [(5954084306217/36893488147419103232),(7144887258043/110680464442257309696),(357243229363/55340232221128654848),(-14593/6917529027641081856),(-367/3458764513820540928)]
  c := (744260538277/4611686018427387904)
  R := (-195493352479771/25000000000000)
  total := (-14619478611/1000000000000000)
  k := 23
  n := 32
  sFloor := (549755571459/1099511627776)
  nFloor := (457329086399/73786976294838206464)
  eFloor := (216948266881/36893488147419103232)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=650171,width:=130034,den:=68719476736,localDen:=110680464442257309696,lowerC:=17862252918648,s:=[110680430548195737600,-13557659860992,-1355682938880],L:=[17862252918651,7144887258043,714486458726,-233488,-11744],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor040Source.source.poly i) 650171 130034 68719476736
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor040Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 10 19) (CoreQuotient.fused G u 10 19) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 10 19 WideAnchor040Source.data
    WideAnchor040Source.path_checked WideAnchor040Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor040Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 19 10) (CoreQuotient.fused G u 19 10) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 19 10 WideAnchor040Source.data
    WideAnchor040Source.path_swapped WideAnchor040Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor040Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor040Cell043
