/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor537Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor537Cell054
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (603851/8589934592)
  b := (724621/8589934592)
  s := [(1098999927823/1099511627776),(-818166381/4398046511104),(-40755189/2199023255552)]
  L := [(2981899779277604217359709/9903520314283042199192993792),(3252884531743/27021597764222976),(162336832081/13510798882111488),(-7669783/1688849860263936),(-190249/844424930131968)]
  c := (1356011025235/4503599627370496)
  R := (-10135106191249/2500000000000)
  total := (-1392014867/25000000000000)
  k := 12
  n := 32
  sFloor := (1098775008633/2199023255552)
  nFloor := (1365361901799/4611686018427387904)
  eFloor := (1055433703665/4611686018427387904)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=603851,width:=120770,den:=8589934592,localDen:=29710560942849126597578981376,lowerC:=8945699337830024777564160,s:=[29696733992543188795678261248,-5527040712898000887742464,-550635161981442412511232],L:=[8945699337832812652079127,3576584366464117472493568,356982468978758974963712,-134928249456299081728,-6693791605528199168],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor537Source.source.poly i) 603851 120770 8589934592
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor537Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 5 15) (CoreQuotient.fused G u 5 15) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 5 15 WideAnchor537Source.data
    WideAnchor537Source.path_checked WideAnchor537Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor537Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 15 5) (CoreQuotient.fused G u 15 5) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 15 5 WideAnchor537Source.data
    WideAnchor537Source.path_swapped WideAnchor537Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor537Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor537Cell054
