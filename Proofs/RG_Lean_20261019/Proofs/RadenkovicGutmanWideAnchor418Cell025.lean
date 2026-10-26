/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor418Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor418Cell025
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1562959/4398046511104)
  b := (937775/2199023255552)
  s := [(4398046511093/4398046511104),(-1/1099511627776)]
  L := [(109673778641517875256827803/85070591730234615865843651857942052864),(116891560921/226673591177742970257408),(46756504687/906694364710971881029632),(1/28334198897217871282176),(-1/56668397794435742564352)]
  c := (1558558134341/1208925819614629174706176)
  R := (-42776550324793/3125000000000)
  total := (-966247361/1000000000000000)
  k := 40
  n := 32
  sFloor := (274877906943/549755813888)
  nFloor := (1553535088707/604462909807314587353088)
  eFloor := (1397920579179/604462909807314587353088)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1562959,width:=312591,den:=4398046511104,localDen:=255211775190703847597530955573826158592,lowerC:=329021335924377330250678272,s:=[255211775190065534764774431369581297664,-232113757366008801543585792],L:=[329021335924553625770483409,131608197551642808055496704,13160786067845003106844672,9007199254740992,-4503599627370496],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor418Source.source.poly i) 1562959 312591 4398046511104
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor418Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 4) (CoreQuotient.fused G u 2 4) (((40/21) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (40/21) 2 4 WideAnchor418Source.data
    WideAnchor418Source.path_checked WideAnchor418Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor418Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 2) (CoreQuotient.fused G u 4 2) (((40/21) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (40/21) 4 2 WideAnchor418Source.data
    WideAnchor418Source.path_swapped WideAnchor418Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor418Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor418Cell025
