/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor029Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor029Cell122
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (558091/32768)
  b := (669709/32768)
  s := [(7191620045803/72057594037927936),(-2044812310989/36028797018963968),(67343957821/4503599627370496)]
  L := [(1188392865092086661779/1180591620717411303424),(-33896488981/13194139533312),(1629086513/2199023255552),(-145723121/824633720832),(3700755/137438953472)]
  c := (552301123579/549755813888)
  R := (230960318859/100000000000000)
  total := (4697412079259/500000000000000)
  k := 0
  n := 32
  sFloor := (130609335905/4503599627370496)
  nFloor := 1098867453829756872287823120444150255122927189939279418627648355463213519635285277337986174267210752142187946211922510455242752
  eFloor := 1091435997531486800233505906396587664840512445173159679754372580317216362886948646828087522710689329019536142355239921927585792
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=558091,width:=111618,den:=32768,localDen:=3541774862152233910272,lowerC:=3558172894973789208576,s:=[353482508491309056,-201013229419462656,52961443437084672],L:=[3565178595276259985337,-9099019476413710336,2623827485883629568,-625876038966050816,95367730173050880],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor029Source.source.poly i) 558091 111618 32768
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor029Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 38) (CoreQuotient.fused G u 9 38) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 38 WideAnchor029Source.data
    WideAnchor029Source.path_checked WideAnchor029Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor029Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 38 9) (CoreQuotient.fused G u 38 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 38 9 WideAnchor029Source.data
    WideAnchor029Source.path_swapped WideAnchor029Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor029Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor029Cell122
