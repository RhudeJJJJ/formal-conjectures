/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor509Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor509Cell068
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (969115/1073741824)
  b := (581469/536870912)
  s := [(2197106773471/2199023255552),(-765041783/2199023255552),(-37823245/1099511627776)]
  L := [(70860860870723735031273/154742504910672534362390528),(2470624975501/13510798882111488),(122700332423/6755399441055744),(-10352537/422212465065984),(-505505/422212465065984)]
  c := (2062322480799/4503599627370496)
  R := (-384439975379089/100000000000000)
  total := (-677071445679/1000000000000000)
  k := 12
  n := 32
  sFloor := (1098133042599/2199023255552)
  nFloor := (1436766559777/18014398509481984)
  eFloor := (1367803287991/18014398509481984)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=969115,width:=193823,den:=1073741824,localDen:=464227514732017603087171584,lowerC:=212582582612095030788096,s:=[463822933420180704677855232,-161505088539452806004736,-15969445508244653998080],L:=[212582582612171205093819,84890027763660769722368,8431902639441815011328,-11382734808481267712,-555808625398906880],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor509Source.source.poly i) 969115 193823 1073741824
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor509Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 39) (CoreQuotient.fused G u 4 39) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 4 39 WideAnchor509Source.data
    WideAnchor509Source.path_checked WideAnchor509Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor509Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 39 4) (CoreQuotient.fused G u 39 4) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 39 4 WideAnchor509Source.data
    WideAnchor509Source.path_swapped WideAnchor509Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor509Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor509Cell068
