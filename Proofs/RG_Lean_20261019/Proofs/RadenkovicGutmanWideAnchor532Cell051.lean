/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor532Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor532Cell051
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1397805/34359738368)
  b := (838683/17179869184)
  s := [(4397796007593/4398046511104),(-50096503/2199023255552),(-625915/274877906944)]
  L := [(298666085865659451118020117/10141204801825835211973625643008),(1697619840629/144115188075855872),(84860933259/72057594037927936),(-501401/9007199254740992),(-12523/4503599627370496)]
  c := (2122150177297/72057594037927936)
  R := (-26081977965397/5000000000000)
  total := (-41679553941/1000000000000000)
  k := 16
  n := 32
  sFloor := (2198842899973/4398046511104)
  nFloor := (74856227939/1152921504606846976)
  eFloor := (289552916593/4611686018427387904)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1397805,width:=279561,den:=34359738368,localDen:=10141204801825835211973625643008,lowerC:=298666085865593788134588416,s:=[10140627180056212376289370177536,-231029342457205693414899712,-23092187633791827999457280],L:=[298666085865659451118020117,119459376276148831341510656,11943114606360779085053952,-564527339190798516224,-28199289066780360704],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor532Source.source.poly i) 1397805 279561 34359738368
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor532Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 5 10) (CoreQuotient.fused G u 5 10) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 5 10 WideAnchor532Source.data
    WideAnchor532Source.path_checked WideAnchor532Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor532Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 10 5) (CoreQuotient.fused G u 10 5) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 10 5 WideAnchor532Source.data
    WideAnchor532Source.path_swapped WideAnchor532Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor532Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor532Cell051
