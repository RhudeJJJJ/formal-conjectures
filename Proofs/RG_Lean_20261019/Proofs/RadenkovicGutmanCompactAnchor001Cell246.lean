/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell246
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (232315/4096)
  b := (511093/8192)
  s := [(3155495933095/1152921504606846976),(-1866304048125/2305843009213693952),(148947909463/1152921504606846976)]
  L := [(18901093099410424669231/18889465931478580854784),(-134598709/1099511627776),(20045611/1099511627776),(-10121/4294967296),(15489/68719476736)]
  c := (550035760887/549755813888)
  R := (5090910159/20000000000000)
  total := (1587253357751/1000000000000000)
  k := 0
  n := 32
  sFloor := (1185645909247/1152921504606846976)
  nFloor := 951102026030392548360766255209709345806263319709388019013541071257804981206515712
  eFloor := 950511744413288514444291061334984624979159192485562282811441610734964662907961344
}

#check "COMPACT_WITNESS_READY"
theorem checked : ComputedPolynomialCell.checks data witness=true := by decide +kernel
#check "COMPACT_CHECK_PASSED"

noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 10)
        (CoreQuotient.fused G u 9 10) ((51/26 : ℚ) : ℝ) y :=
  ComputedPolynomialCell.computed_actual_integral (51/26) 9 10 witness checked G u hd
#print axioms checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell246
