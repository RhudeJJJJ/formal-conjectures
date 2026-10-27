/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor028Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor028Cell127
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1388707/32768)
  b := (104153/2048)
  s := [(7556188364685/1152921504606846976),(-1081786848919/288230376151711744),(286696200369/288230376151711744)]
  L := [(4727552382735793079689/4722366482869645213696),(-359237201/824633720832),(141438433/1099511627776),(-12962879/412316860416),(335413/68719476736)]
  c := (68772019913/68719476736)
  R := (7643116969/20000000000000)
  total := (3881627925687/1000000000000000)
  k := 0
  n := 32
  sFloor := (1093956442621/576460752303423488)
  nFloor := 10996572970101525043653106329022247672461207728080579477549927887907140792354195001220308234414557276235704919012864198610063281241011742465436353845086365390209024
  eFloor := 10984366224348798065271422936786080643401377561381532044561193578438799634970069066349268630806132342919410403785826515266905125816955688557461830167545170284773376
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1388707,width:=277741,den:=32768,localDen:=14167099448608935641088,lowerC:=14177931667497396731904,s:=[92850442625249280,-53171987198066688,14091691640537088],L:=[14182657148207379239067,-6171648119206313984,1822420332397461504,-445401130936041472,69148217551355904],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor028Source.source.poly i) 1388707 277741 32768
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor028Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 37) (CoreQuotient.fused G u 9 37) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 37 WideAnchor028Source.data
    WideAnchor028Source.path_checked WideAnchor028Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor028Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 37 9) (CoreQuotient.fused G u 37 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 37 9 WideAnchor028Source.data
    WideAnchor028Source.path_swapped WideAnchor028Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor028Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor028Cell127
