/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanSymbolicAnchor010Source
namespace Gebendorfer.RadenkovicGutman.SymbolicAnchor010Cell127
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (90327/134217728)
  b := (1589755/2147483648)
  s := [(2148003521629/2199023255552),(-19696859517/4398046511104),(-413589567/2199023255552)]
  L := [(164394344781926480954251/9671406556917033397649408),(2802235801603/844424930131968),(63410506913/422212465065984),(-78279037/52776558133248),(-651749/26388279066624)]
  c := (299031571161/17592186044416)
  R := (-203733047535371/100000000000000)
  total := (-133934826651/1000000000000000)
  k := 6
  n := 32
  sFloor := (2137741502303/4398046511104)
  nFloor := (731108343239/18014398509481984)
  eFloor := (1009625651367/36028797018963968)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1445232,width:=144523,den:=2147483648,localDen:=29014219670751100192948224,lowerC:=493183034345468832251904,s:=[28341058182418586558005248,-129941556417671202865152,-5456958456520092155904],L:=[493183034345779442862753,96284088988521835003904,4357536854625870675968,-43034355696303865856,-716605603891380224],transformed:=fun i => IntegerPolynomialPaymentCell.affine (SymbolicAnchor010Source.source.poly i) 1445232 144523 2147483648
}
theorem checked : IntegerPolynomialPaymentCell.checks SymbolicAnchor010Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 19) (CoreQuotient.fused G u 9 19) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 19 SymbolicAnchor010Source.data
    SymbolicAnchor010Source.path_checked SymbolicAnchor010Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry SymbolicAnchor010Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 19 9) (CoreQuotient.fused G u 19 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 19 9 SymbolicAnchor010Source.data
    SymbolicAnchor010Source.path_swapped SymbolicAnchor010Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry SymbolicAnchor010Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.SymbolicAnchor010Cell127
