/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor032Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor032Cell083
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (466597/33554432)
  b := (139979/8388608)
  s := [(4542000598885/8796093022208),(-16347924015/274877906944),(9032771341/1099511627776)]
  L := [(99095684196895128597/295147905179352825856),(363623410279/6597069766656),(-10988225257/1649267441664),(79475053/206158430208),(116711/12884901888)]
  c := (184580095479/549755813888)
  R := (-10913907137771/20000000000000)
  total := (-88572568643/62500000000000)
  k := 2
  n := 32
  sFloor := (1022782300283/4398046511104)
  nFloor := (728438804811/70368744177664)
  eFloor := (86497023843/8796093022208)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=466597,width:=93319,den:=33554432,localDen:=885443715538058477568,lowerC:=297287052590573420544,s:=[457212750717738024960,-52660349251438510080,7274148281595199488],L:=[297287052590685385791,48804707975259226112,-5899258514987024384,341342753482866688,8020318849335296],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor032Source.source.poly i) 466597 93319 33554432
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor032Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 10 11) (CoreQuotient.fused G u 10 11) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 10 11 WideAnchor032Source.data
    WideAnchor032Source.path_checked WideAnchor032Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor032Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 11 10) (CoreQuotient.fused G u 11 10) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 11 10 WideAnchor032Source.data
    WideAnchor032Source.path_swapped WideAnchor032Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor032Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor032Cell083
