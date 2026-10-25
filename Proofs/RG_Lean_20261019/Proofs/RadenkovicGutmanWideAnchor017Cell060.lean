/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor017Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor017Cell060
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (901543/4294967296)
  b := (1081851/4294967296)
  s := [(1098662930311/1099511627776),(-1356337459/4398046511104),(-67380797/2199023255552)]
  L := [(253737546729036075044235/618970019642690137449562112),(4427173742149/27021597764222976),(220628247289/13510798882111488),(-18208585/1688849860263936),(-449137/844424930131968)]
  c := (1846183635127/4503599627370496)
  R := (-38997558323693/10000000000000)
  total := (-39946298003/250000000000000)
  k := 12
  n := 32
  sFloor := (2196580311095/4398046511104)
  nFloor := (261278667855/72057594037927936)
  eFloor := (492163672181/144115188075855872)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=901543,width:=180308,den:=4294967296,localDen:=1856910058928070412348686336,lowerC:=761212640186962733432832,s:=[1855476736332898805634564096,-572662582025723005894656,-56898024798961319018496],L:=[761212640187108225132705,304233062979838268145664,30322915413761781137408,-20020550932847656960,-987662707928858624],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor017Source.source.poly i) 901543 180308 4294967296
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor017Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 26) (CoreQuotient.fused G u 9 26) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 26 WideAnchor017Source.data
    WideAnchor017Source.path_checked WideAnchor017Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor017Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 26 9) (CoreQuotient.fused G u 26 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 26 9 WideAnchor017Source.data
    WideAnchor017Source.path_swapped WideAnchor017Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor017Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor017Cell060
