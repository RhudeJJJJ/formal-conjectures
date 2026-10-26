/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor519Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor519Cell011
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (60867/2199023255552)
  b := (584323/17592186044416)
  s := [(4398046511103/4398046511104)]
  L := [(886362156811/154742504910672534362390528),(709088269221/309485009821345068724781056),(17727170325/77371252455336267181195264)]
  c := (886362156811/154742504910672534362390528)
  R := (-1639670662490779/100000000000000)
  total := (-90250169/1000000000000000)
  k := 48
  n := 32
  sFloor := (2199023255551/4398046511104)
  nFloor := (801795998693/77371252455336267181195264)
  eFloor := (1283192399571/77371252455336267181195264)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=486936,width:=97387,den:=17592186044416,localDen:=309485009821345068724781056,lowerC:=1772724313622,s:=[309485009821274699980603392],L:=[1772724313622,709088269221,70908681300],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor519Source.source.poly i) 486936 97387 17592186044416
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor519Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 4) (CoreQuotient.fused G u 4 4) (((15/8) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (15/8) 4 4 WideAnchor519Source.data
    WideAnchor519Source.path_checked WideAnchor519Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor519Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 4) (CoreQuotient.fused G u 4 4) (((15/8) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (15/8) 4 4 WideAnchor519Source.data
    WideAnchor519Source.path_swapped WideAnchor519Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor519Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor519Cell011
