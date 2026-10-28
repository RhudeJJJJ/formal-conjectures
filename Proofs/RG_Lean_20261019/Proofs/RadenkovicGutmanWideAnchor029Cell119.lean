/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor029Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor029Cell119
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1291879/131072)
  b := (775127/65536)
  s := [(4514528162821/9007199254740992),(-5052337376119/18014398509481984),(656633773315/9007199254740992)]
  L := [(601404050173931257777/590295810358705651712),(-46458152315/6597069766656),(6383549395/3298534883328),(-180574633/412316860416),(13175669/206158430208)]
  c := (278543974769/274877906944)
  R := (132489212031/20000000000000)
  total := (968369225981/62500000000000)
  k := 0
  n := 32
  sFloor := (661248312019/4503599627370496)
  nFloor := 1283830770604969422783131660401581667934997287353115734163542438240579792787579253135860336724635811840
  eFloor := 1258855160198137598976715077862187218522027039676734627718286102493247546299734245920366549101765984256
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1291879,width:=258375,den:=131072,localDen:=1770887431076116955136,lowerC:=1794505893196056231936,s:=[887592353035911168,-496664973422002176,129099452903915520],L:=[1804212150521793773331,-12471015301594480640,3427141985490698240,-775562143222202368,113178134915842048],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor029Source.source.poly i) 1291879 258375 131072
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor029Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 38) (CoreQuotient.fused G u 9 38) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 38 WideAnchor029Source.data
    WideAnchor029Source.path_checked WideAnchor029Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor029Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 38 9) (CoreQuotient.fused G u 38 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 38 9 WideAnchor029Source.data
    WideAnchor029Source.path_swapped WideAnchor029Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor029Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor029Cell119
