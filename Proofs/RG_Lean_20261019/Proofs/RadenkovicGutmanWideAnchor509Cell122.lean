/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor509Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor509Cell122
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (558091/32768)
  b := (669709/32768)
  s := [(7191620045807/72057594037927936),(-4089624621987/72057594037927936),(538751662571/36028797018963968)]
  L := [(1188392865023847963969/1180591620717411303424),(-33896488981/13194139533312),(1629086513/2199023255552),(-145723121/824633720832),(3700755/137438953472)]
  c := (1104602247095/1099511627776)
  R := (230960316007/100000000000000)
  total := (4697412030303/500000000000000)
  k := 0
  n := 32
  sFloor := (2089749374481/72057594037927936)
  nFloor := 151001055248278184912389577116112093509005494016874931757425675527642364732536870107833814571264727760768905810804736
  eFloor := 149979860436113137806846082186014848159223140630844615819753643420035356992239362027560289202189715538527915442438144
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=558091,width:=111618,den:=32768,localDen:=3541774862152233910272,lowerC:=3558172894770852003840,s:=[353482508491505664,-201013229419905024,52961443437379584],L:=[3565178595071543891907,-9099019476413710336,2623827485883629568,-625876038966050816,95367730173050880],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor509Source.source.poly i) 558091 111618 32768
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor509Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 39) (CoreQuotient.fused G u 4 39) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 4 39 WideAnchor509Source.data
    WideAnchor509Source.path_checked WideAnchor509Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor509Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 39 4) (CoreQuotient.fused G u 39 4) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 39 4 WideAnchor509Source.data
    WideAnchor509Source.path_swapped WideAnchor509Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor509Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor509Cell122
