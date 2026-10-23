/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor004Cell246
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 13
def witness : ComputedPolynomialCell.Witness := {
  a := (232315/4096)
  b := (511093/8192)
  s := [(3155495933095/1152921504606846976),(-1866304048125/2305843009213693952),(148947909463/1152921504606846976)]
  L := [(75604372397697176729127/75557863725914323419136),(-134598709/1099511627776),(20045611/1099511627776),(-10121/4294967296),(15489/68719476736)]
  c := (1100071521775/1099511627776)
  R := (636363771/2500000000000)
  total := (793626679903/500000000000000)
  k := 0
  n := 32
  sFloor := (1185645909247/1152921504606846976)
  nFloor := 31720584509894638257083772861330376885727331909342183477813158694972133694423002094027931648
  eFloor := 31700897791320380335453945700604609901134592105831811758739501216704429369437002450813845504
}

#check "COMPACT_WITNESS_READY"
theorem checked : ComputedPolynomialCell.checks data witness=true := by decide +kernel
#check "COMPACT_CHECK_PASSED"

noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 13)
        (CoreQuotient.fused G u 9 13) ((51/26 : ℚ) : ℝ) y :=
  ComputedPolynomialCell.computed_actual_integral (51/26) 9 13 witness checked G u hd
#print axioms checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.CompactAnchor004Cell246
