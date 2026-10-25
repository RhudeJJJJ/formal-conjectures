/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor231Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor231Cell026
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (937775/2199023255552)
  b := (562665/1099511627776)
  s := [(2199023255467/2199023255552),(-33/2199023255552),(-1/549755813888)]
  L := [(2435837413422821640580325/166153499473114484112975882535043072),(1772304977397/302231454903657293676544),(88615248833/151115727451828646838272),(3/18889465931478580854784),(-1/9444732965739290427392)]
  c := (4326916449/295147905179352825856)
  R := (-38977948889523/3125000000000)
  total := (-131978081/125000000000000)
  k := 36
  n := 32
  sFloor := (1099511627715/2199023255552)
  nFloor := (695363714587/151115727451828646838272)
  eFloor := (913579201417/151115727451828646838272)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=937775,width:=187555,den:=2199023255552,localDen:=166153499473114484112975882535043072,lowerC:=2435837413422458719961088,s:=[166153499466692065696273165044416512,-2493409502955172672831488,-302231454903657293676544],L:=[2435837413422821640580325,974334965306641178689536,97433496490147114385408,26388279066624,-17592186044416],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor231Source.source.poly i) 937775 187555 2199023255552
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor231Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 14) (CoreQuotient.fused G u 0 14) (((17/9) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (17/9) 0 14 WideAnchor231Source.data
    WideAnchor231Source.path_checked WideAnchor231Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor231Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 14 0) (CoreQuotient.fused G u 14 0) (((17/9) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (17/9) 14 0 WideAnchor231Source.data
    WideAnchor231Source.path_swapped WideAnchor231Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor231Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor231Cell026
