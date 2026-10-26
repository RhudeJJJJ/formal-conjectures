/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor268Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor268Cell000
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1/268435456)
  b := (1258291/281474976710656)
  s := [(4398046511103/4398046511104)]
  L := [(813785318343/77371252455336267181195264),(1953082901407/464227514732017603087171584),(97654051961/232113757366008801543585792),(-1/7253554917687775048237056),(1/14507109835375550096474112)]
  c := (813785318343/77371252455336267181195264)
  R := (-804642377416759/50000000000000)
  total := (-11920259/1000000000000000)
  k := 47
  n := 32
  sFloor := (2199023255551/4398046511104)
  nFloor := (182504527683/154742504910672534362390528)
  eFloor := (400481494179/309485009821345068724781056)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1048576,width:=209715,den:=281474976710656,localDen:=464227514732017603087171584,lowerC:=4882711910058,s:=[464227514731912049970905088],L:=[4882711910058,1953082901407,195308103922,-64,32],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor268Source.source.poly i) 1048576 209715 281474976710656
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor268Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 44) (CoreQuotient.fused G u 0 44) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 44 WideAnchor268Source.data
    WideAnchor268Source.path_checked WideAnchor268Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor268Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 44 0) (CoreQuotient.fused G u 44 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 44 0 WideAnchor268Source.data
    WideAnchor268Source.path_swapped WideAnchor268Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor268Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor268Cell000
