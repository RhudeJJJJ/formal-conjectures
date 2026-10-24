/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanSymbolicAnchor014Source
namespace Gebendorfer.RadenkovicGutman.SymbolicAnchor014Cell127
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (90327/134217728)
  b := (1589755/2147483648)
  s := [(2146896049911/2199023255552),(-5027069707/1099511627776),(-210236071/1099511627776)]
  L := [(85173231849667977701313/4835703278458516698824704),(967357841909/281474976710656),(65513223221/422212465065984),(-27599601/17592186044416),(-681845/26388279066624)]
  c := (619716824801/35184372088832)
  R := (-100977366218469/50000000000000)
  total := (-132739927299/1000000000000000)
  k := 6
  n := 32
  sFloor := (2136421438355/4398046511104)
  nFloor := (834889957545/18014398509481984)
  eFloor := (568549839613/18014398509481984)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1445232,width:=144523,den:=2147483648,localDen:=14507109835375550096474112,lowerC:=255519695548920643977216,s:=[14163223023021048899567616,-66327859157843872579584,-2773884055709288497152],L:=[255519695549003933103939,49857243534339518496768,2251017209517942243328,-22759561666108588032,-374848252920463360],transformed:=fun i => IntegerPolynomialPaymentCell.affine (SymbolicAnchor014Source.source.poly i) 1445232 144523 2147483648
}
theorem checked : IntegerPolynomialPaymentCell.checks SymbolicAnchor014Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 23) (CoreQuotient.fused G u 9 23) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 23 SymbolicAnchor014Source.data
    SymbolicAnchor014Source.path_checked SymbolicAnchor014Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry SymbolicAnchor014Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 23 9) (CoreQuotient.fused G u 23 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 23 9 SymbolicAnchor014Source.data
    SymbolicAnchor014Source.path_swapped SymbolicAnchor014Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry SymbolicAnchor014Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.SymbolicAnchor014Cell127
