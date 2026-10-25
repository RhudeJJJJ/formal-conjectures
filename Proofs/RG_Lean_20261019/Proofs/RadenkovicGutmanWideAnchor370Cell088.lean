/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor370Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor370Cell088
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (72565/2097152)
  b := (43539/1048576)
  s := [(2025891429/2147483648),(-89955483421/4398046511104),(-2326615653/2199023255552)]
  L := [(414999326960999358453/18889465931478580854784),(7122129290575/844424930131968),(301425036335/422212465065984),(-1150257553/52776558133248),(-1900979/26388279066624)]
  c := (386498241649/17592186044416)
  R := (-7636165578189/4000000000000)
  total := (-3147852413563/250000000000000)
  k := 6
  n := 32
  sFloor := (506802116483/1099511627776)
  nFloor := (992433953107/35184372088832)
  eFloor := (82256888989/2199023255552)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=72565,width:=14513,den:=2097152,localDen:=56668397794435742564352,lowerC:=1244997980882970083328,s:=[53459788387133681565696,-1159067578167195598848,-59956428839980105728],L:=[1244997980882998075359,477958005951614156800,40456583539201146880,-1235079643027996672,-4082321317691392],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor370Source.source.poly i) 72565 14513 2097152
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor370Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 10) (CoreQuotient.fused G u 2 10) (((21/11) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (21/11) 2 10 WideAnchor370Source.data
    WideAnchor370Source.path_checked WideAnchor370Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor370Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 10 2) (CoreQuotient.fused G u 10 2) (((21/11) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (21/11) 10 2 WideAnchor370Source.data
    WideAnchor370Source.path_swapped WideAnchor370Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor370Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor370Cell088
