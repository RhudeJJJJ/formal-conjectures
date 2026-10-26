/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor424Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor424Cell062
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1298221/4294967296)
  b := (1557865/4294967296)
  s := [(4398036303425/4398046511104),(-4083057/4398046511104),(-204149/2199023255552)]
  L := [(783747132644551257815944599/649037107316853453566312041152512),(2227538950969/4611686018427387904),(334128989161/6917529027641081856),(-13303/288230376151711744),(-997/432345564227567616)]
  c := (1392214579433/1152921504606846976)
  R := (-681345700787231/100000000000000)
  total := (-203114027477/500000000000000)
  k := 20
  n := 32
  sFloor := (2199015906035/4398046511104)
  nFloor := (1221510564469/576460752303423488)
  eFloor := (1173892841261/576460752303423488)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1298221,width:=259644,den:=4294967296,localDen:=1947111321950560360698936123457536,lowerC:=2351241397932836476617228288,s:=[1947106802787949970792325002035200,-1807658580416839216621682688,-180762449083379100137029632],L:=[2351241397933653773447833797,940494711519117558725738496,94048949442447506057199616,-89867078764364562432,-4490088828488384512],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor424Source.source.poly i) 1298221 259644 4294967296
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor424Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 6) (CoreQuotient.fused G u 2 6) (((48/25) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (48/25) 2 6 WideAnchor424Source.data
    WideAnchor424Source.path_checked WideAnchor424Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor424Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 6 2) (CoreQuotient.fused G u 6 2) (((48/25) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (48/25) 6 2 WideAnchor424Source.data
    WideAnchor424Source.path_swapped WideAnchor424Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor424Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor424Cell062
