/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor506Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor506Cell066
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (672997/1073741824)
  b := (201899/268435456)
  s := [(4396880698625/4398046511104),(-233002295/2199023255552),(-1450733/137438953472)]
  L := [(7515350288194308090593915/79228162514264337593543950336),(2049473221019/54043195528445952),(51129539425/13510798882111488),(-5350757/3377699720527872),(-66331/844424930131968)]
  c := (854396408635/9007199254740992)
  R := (-57894621674439/12500000000000)
  total := (-284423962749/500000000000000)
  k := 14
  n := 32
  sFloor := (2198184135289/4398046511104)
  nFloor := (432372263205/18014398509481984)
  eFloor := (1208410883053/36028797018963968)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=672997,width:=134599,den:=1073741824,localDen:=237684487542793012780631851008,lowerC:=22546050864581695493898240,s:=[237621483311040913490313216000,-25184377174523289198919680,-2508871909714207401050112],L:=[22546050864582924271781745,9013678549303690029694976,899480369929902673100800,-376526050489844891648,-18670516680194523136],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor506Source.source.poly i) 672997 134599 1073741824
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor506Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 36) (CoreQuotient.fused G u 4 36) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 4 36 WideAnchor506Source.data
    WideAnchor506Source.path_checked WideAnchor506Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor506Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 36 4) (CoreQuotient.fused G u 36 4) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 36 4 WideAnchor506Source.data
    WideAnchor506Source.path_swapped WideAnchor506Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor506Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor506Cell066
