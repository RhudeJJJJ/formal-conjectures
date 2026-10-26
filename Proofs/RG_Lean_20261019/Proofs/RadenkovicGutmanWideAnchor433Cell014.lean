/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor433Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor433Cell014
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (841425/17592186044416)
  b := (504855/8796093022208)
  s := [(4398046511103/4398046511104)]
  L := [(4577428787143/154742504910672534362390528),(5492914544591/464227514732017603087171584),(91548575721/77371252455336267181195264),(13/29014219670751100192948224),(-1/4835703278458516698824704)]
  c := (1144357196785/38685626227668133590597632)
  R := (-97348894226539/6250000000000)
  total := (-2962001/20000000000000)
  k := 45
  n := 32
  sFloor := (2199023255551/4398046511104)
  nFloor := (1034692061189/38685626227668133590597632)
  eFloor := (559386500565/9671406556917033397649408)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=841425,width:=168285,den:=17592186044416,localDen:=464227514732017603087171584,lowerC:=13732286361420,s:=[464227514731912049970905088],L:=[13732286361429,5492914544591,549291454326,208,-96],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor433Source.source.poly i) 841425 168285 17592186044416
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor433Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 8) (CoreQuotient.fused G u 2 8) (((13/7) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (13/7) 2 8 WideAnchor433Source.data
    WideAnchor433Source.path_checked WideAnchor433Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor433Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 8 2) (CoreQuotient.fused G u 8 2) (((13/7) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (13/7) 8 2 WideAnchor433Source.data
    WideAnchor433Source.path_swapped WideAnchor433Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor433Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor433Cell014
