/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor026Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor026Cell095
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (260013/2097152)
  b := (624031/4194304)
  s := [(4655833455803/17592186044416),(217808368641/17592186044416),(-28524349551/8796093022208)]
  L := [(205768494700996928837/295147905179352825856),(-72959995483/3298534883328),(65286589321/6597069766656),(-646882807/412316860416),(68591855/412316860416)]
  c := (751566367559/1099511627776)
  R := (-19023093335301/100000000000000)
  total := (-4617845908739/1000000000000000)
  k := 1
  n := 32
  sFloor := (581979181975/4398046511104)
  nFloor := (478947630951/8589934592)
  eFloor := (1597825292297/34359738368)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=520026,width:=104005,den:=4194304,localDen:=885443715538058477568,lowerC:=605241181769891315712,s:=[234335770644100153344,10962654141893050368,-2871355042059780096],L:=[617305484102990786511,-19585049657237045248,8762617687533682688,-1389170250204839936,147299886998487040],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor026Source.source.poly i) 520026 104005 4194304
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor026Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 35) (CoreQuotient.fused G u 9 35) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 35 WideAnchor026Source.data
    WideAnchor026Source.path_checked WideAnchor026Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor026Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 35 9) (CoreQuotient.fused G u 35 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 35 9 WideAnchor026Source.data
    WideAnchor026Source.path_swapped WideAnchor026Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor026Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor026Cell095
