/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor432Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor432Cell103
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1118005/2097152)
  b := (670803/1048576)
  s := [(3797991718973/17592186044416),(-1568348511647/35184372088832),(101316266499/17592186044416)]
  L := [(129578958204403301819/147573952589676412928),(884800046301/8796093022208),(-68072996807/4398046511104),(973157237/549755813888),(-44111733/274877906944)]
  c := (965438471767/1099511627776)
  R := (-1625487655267/25000000000000)
  total := (-851223553987/200000000000000)
  k := 1
  n := 32
  sFloor := (194695858103/2199023255552)
  nFloor := (144168365441/134217728)
  eFloor := (1694131421911/2147483648)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1118005,width:=223601,den:=2097152,localDen:=147573952589676412928,lowerC:=129578958204358885376,s:=[31859863717710659584,-6578130435795058688,849902443683643392],L:=[129578958204403301819,14844481493601878016,-2284150742396698624,261229906673795072,-23682306325610496],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor432Source.source.poly i) 1118005 223601 2097152
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor432Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 8) (CoreQuotient.fused G u 2 8) (((32/17) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (32/17) 2 8 WideAnchor432Source.data
    WideAnchor432Source.path_checked WideAnchor432Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor432Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 8 2) (CoreQuotient.fused G u 8 2) (((32/17) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (32/17) 8 2 WideAnchor432Source.data
    WideAnchor432Source.path_swapped WideAnchor432Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor432Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor432Cell103
