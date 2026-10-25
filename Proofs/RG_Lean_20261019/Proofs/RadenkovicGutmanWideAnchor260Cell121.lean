/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor260Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor260Cell121
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (116269/8192)
  b := (558091/32768)
  s := [(3103086577933/18014398509481984),(-440843814003/4503599627370496),(116082096537/4503599627370496)]
  L := [(595874975916899068705/590295810358705651712),(-3018251069/824633720832),(1155477145/1099511627776),(-102927239/412316860416),(2606005/68719476736)]
  c := (276700499817/274877906944)
  R := (165216720239/50000000000000)
  total := (5595857410961/500000000000000)
  k := 0
  n := 32
  sFloor := (1804039708069/36028797018963968)
  nFloor := 88411562169410793202274158187480335965270559114367341481597294241340684087358716781408542523392
  eFloor := 87553595348838240164020366733584799073023382289526862545020090800266749407861844676013774077952
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=465076,width:=93015,den:=32768,localDen:=1770887431076116955136,lowerC:=1782629396251303477248,s:=[305045822957125632,-173346841167003648,45645337671892992],L:=[1787624927750697206115,-6481644816236019712,1861026205893918720,-442069125372575744,67156237489274880],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor260Source.source.poly i) 465076 93015 32768
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor260Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 37) (CoreQuotient.fused G u 0 37) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 37 WideAnchor260Source.data
    WideAnchor260Source.path_checked WideAnchor260Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor260Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 37 0) (CoreQuotient.fused G u 37 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 37 0 WideAnchor260Source.data
    WideAnchor260Source.path_swapped WideAnchor260Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor260Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor260Cell121
