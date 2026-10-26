/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor424Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor424Cell034
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (15751/8589934592)
  b := (302419/137438953472)
  s := [(549755813841/549755813888),(-151/4398046511104),(-7/2199023255552)]
  L := [(1890233370160934494022866601/42535295865117307932921825928971026432),(2014629390905/113336795588871485128704),(100731069851/56668397794435742564352),(-5/7083549724304467820544),(1/3541774862152233910272)]
  c := (1678864487573/37778931862957161709568)
  R := (-148980623508937/12500000000000)
  total := (-4336479831/1000000000000000)
  k := 35
  n := 32
  sFloor := (2199023255281/4398046511104)
  nFloor := (1473007264889/18889465931478580854784)
  eFloor := (707793261775/9444732965739290427392)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=252016,width:=50403,den:=137438953472,localDen:=127605887595351923798765477786913079296,lowerC:=5670700110479491134344134656,s:=[127605887584442577202563064114364547072,-4381147170283416129135181824,-406199075390515402701275136],L:=[5670700110482803482068599803,2268271043542351830811934720,226826204322797502016258048,-90071992547409920,36028797018963968],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor424Source.source.poly i) 252016 50403 137438953472
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor424Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 6) (CoreQuotient.fused G u 2 6) (((48/25) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (48/25) 2 6 WideAnchor424Source.data
    WideAnchor424Source.path_checked WideAnchor424Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor424Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 6 2) (CoreQuotient.fused G u 6 2) (((48/25) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (48/25) 6 2 WideAnchor424Source.data
    WideAnchor424Source.path_swapped WideAnchor424Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor424Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor424Cell034
