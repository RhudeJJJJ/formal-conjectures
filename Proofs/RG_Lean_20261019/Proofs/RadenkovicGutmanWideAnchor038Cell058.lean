/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor038Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor038Cell058
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (78259/536870912)
  b := (375643/2147483648)
  s := [(2198829655095/2199023255552),(-154856613/4398046511104),(-7736351/2199023255552)]
  L := [(235516943899328912559256131/5070602400912917605986812821504),(2007905343701/108086391056891904),(33449885189/18014398509481984),(-1132001/6755399441055744),(-9417/1125899906842624)]
  c := (209181067045/4503599627370496)
  R := (-498859366288623/100000000000000)
  total := (-28540691071/200000000000000)
  k := 15
  n := 32
  sFloor := (2198744490437/4398046511104)
  nFloor := (1595909211961/1152921504606846976)
  eFloor := (1512555294235/1152921504606846976)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=313036,width:=62607,den:=2147483648,localDen:=15211807202738752817960438464512,lowerC:=706550831697618555623178240,s:=[15210467965957690738881142456320,-535612557774840657937956864,-53516432610520111257747456],L:=[706550831697986737677768393,282587554927720353054588928,28245916963643676218621952,-2549039640891514421248,-127231193072843882496],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor038Source.source.poly i) 313036 62607 2147483648
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor038Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 10 17) (CoreQuotient.fused G u 10 17) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 10 17 WideAnchor038Source.data
    WideAnchor038Source.path_checked WideAnchor038Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor038Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 17 10) (CoreQuotient.fused G u 17 10) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 17 10 WideAnchor038Source.data
    WideAnchor038Source.path_swapped WideAnchor038Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor038Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor038Cell058
