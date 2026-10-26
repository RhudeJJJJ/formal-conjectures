/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor527Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor527Cell057
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (521727/4294967296)
  b := (78259/536870912)
  s := [(4396789586151/4398046511104),(-502552575/4398046511104),(-25067773/2199023255552)]
  L := [(11921863290471614716146269/79228162514264337593543950336),(2167904931757/36028797018963968),(324788010827/54043195528445952),(-3301735/2251799813685248),(-246407/3377699720527872)]
  c := (1355358937243/9007199254740992)
  R := (-220042828404049/50000000000000)
  total := (-104641134783/1000000000000000)
  k := 13
  n := 32
  sFloor := (2198118449015/4398046511104)
  nFloor := (1073632514041/2305843009213693952)
  eFloor := (1019700657303/2305843009213693952)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=521727,width:=104345,den:=4294967296,localDen:=237684487542793012780631851008,lowerC:=35765589871411208631877632,s:=[237616559301793451042251210752,-27159547074048998925926400,-2709485115403396335009792],L:=[35765589871414844148438807,14301820082278543594094592,1428432777866095527723008,-348508418336159170560,-17339351146585653248],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor527Source.source.poly i) 521727 104345 4294967296
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor527Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 7) (CoreQuotient.fused G u 4 7) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 4 7 WideAnchor527Source.data
    WideAnchor527Source.path_checked WideAnchor527Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor527Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 7 4) (CoreQuotient.fused G u 7 4) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 7 4 WideAnchor527Source.data
    WideAnchor527Source.path_swapped WideAnchor527Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor527Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor527Cell057
