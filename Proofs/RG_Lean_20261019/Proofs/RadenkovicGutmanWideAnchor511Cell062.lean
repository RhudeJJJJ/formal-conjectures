/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor511Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor511Cell062
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1298221/4294967296)
  b := (1557865/4294967296)
  s := [(4397641110847/4398046511104),(-40531195/1099511627776),(-4048233/1099511627776)]
  L := [(244121296557946790463527243/5070602400912917605986812821504),(4162249057927/216172782113783808),(207961427785/108086391056891904),(-3770281/13510798882111488),(-94021/6755399441055744)]
  c := (1734586139135/36028797018963968)
  R := (-12426631208057/2500000000000)
  total := (-294825993149/1000000000000000)
  k := 15
  n := 32
  sFloor := (2198731396567/4398046511104)
  nFloor := (1335315496545/144115188075855872)
  eFloor := (319589137311/36028797018963968)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1298221,width:=259644,den:=4294967296,localDen:=15211807202738752817960438464512,lowerC:=732363889673476249579683840,s:=[15210405018715947490616348246016,-560751435874962157432995840,-56007538576309079450320896],L:=[732363889673840371390581729,292892239160988050315542528,29267969021248822291988480,-4244959026670515257344,-211716470282500702208],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor511Source.source.poly i) 1298221 259644 4294967296
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor511Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 41) (CoreQuotient.fused G u 4 41) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 4 41 WideAnchor511Source.data
    WideAnchor511Source.path_checked WideAnchor511Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor511Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 41 4) (CoreQuotient.fused G u 41 4) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 41 4 WideAnchor511Source.data
    WideAnchor511Source.path_swapped WideAnchor511Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor511Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor511Cell062
