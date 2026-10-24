/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanSymbolicAnchor022Source
namespace Gebendorfer.RadenkovicGutman.SymbolicAnchor022Cell127
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (90327/134217728)
  b := (1589755/2147483648)
  s := [(2136695644343/2199023255552),(-23870253867/4398046511104),(-480531831/2199023255552)]
  L := [(103225409711849526521355/4835703278458516698824704),(3499850812613/844424930131968),(25782884989/140737488355328),(-117915143/52776558133248),(-291609/8796093022208)]
  c := (375531852885/17592186044416)
  R := (-6010729394003/3125000000000)
  total := (-126288173459/1000000000000000)
  k := 6
  n := 32
  sFloor := (1062139992789/2199023255552)
  nFloor := (517201343549/9007199254740992)
  eFloor := (696597696187/18014398509481984)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1445232,width:=144523,den:=2147483648,localDen:=14507109835375550096474112,lowerC:=309676229135492783800320,s:=[14095930235840766576427008,-78736865054194585829376,-3170102014205950427136],L:=[309676229135548579564065,60126979124207437217792,2657679547782823673856,-32412267704842452992,-480941229396197376],transformed:=fun i => IntegerPolynomialPaymentCell.affine (SymbolicAnchor022Source.source.poly i) 1445232 144523 2147483648
}
theorem checked : IntegerPolynomialPaymentCell.checks SymbolicAnchor022Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 31) (CoreQuotient.fused G u 9 31) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 31 SymbolicAnchor022Source.data
    SymbolicAnchor022Source.path_checked SymbolicAnchor022Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry SymbolicAnchor022Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 31 9) (CoreQuotient.fused G u 31 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 31 9 SymbolicAnchor022Source.data
    SymbolicAnchor022Source.path_swapped SymbolicAnchor022Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry SymbolicAnchor022Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.SymbolicAnchor022Cell127
