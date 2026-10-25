/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor505Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor505Cell116
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (23363/4096)
  b := (897139/131072)
  s := [(5395948183827/2251799813685248),(-2887292274843/2251799813685248),(361366908549/1125899906842624)]
  L := [(619929742982491411421/590295810358705651712),(-55942993523/3298534883328),(2223984997/549755813888),(-316544549/412316860416),(813397/8589934592)]
  c := (1139769430135/1099511627776)
  R := (14046828599/781250000000)
  total := (5988429793029/250000000000000)
  k := 0
  n := 32
  sFloor := (1615694863041/2251799813685248)
  nFloor := 2678672290533179808923600559928835312184800743616511388846152220672
  eFloor := 2538431258607708753356492449989294585837410964067664339297474969600
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=747616,width:=149523,den:=131072,localDen:=1770887431076116955136,lowerC:=1835727160278893199360,s:=[4243546322103435264,-2270659038289330176,568381001248014336],L:=[1859789228947474234263,-30034165952703102976,7163957121682243584,-1359548485682069504,167688648655896576],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor505Source.source.poly i) 747616 149523 131072
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor505Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 35) (CoreQuotient.fused G u 4 35) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 4 35 WideAnchor505Source.data
    WideAnchor505Source.path_checked WideAnchor505Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor505Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 35 4) (CoreQuotient.fused G u 35 4) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 35 4 WideAnchor505Source.data
    WideAnchor505Source.path_swapped WideAnchor505Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor505Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor505Cell116
