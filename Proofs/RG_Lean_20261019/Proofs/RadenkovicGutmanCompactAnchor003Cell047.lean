/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor003Cell047
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 12
def witness : ComputedPolynomialCell.Witness := {
  a := (1445001/4398046511104)
  b := (1589501/4398046511104)
  s := [(549755813123/549755813888),(-1223/4398046511104),(-31/2199023255552)]
  L := [(6869177503715/9444732965739290427392),(1373834547903/9444732965739290427392),(103037519125/14167099448608935641088),(-1/590295810358705651712),(-1/885443715538058477568)]
  c := (214661796991/295147905179352825856)
  R := (-526041967219387/50000000000000)
  total := (-172038493/500000000000000)
  k := 31
  n := 32
  sFloor := (2199023251849/4398046511104)
  nFloor := (212573392163/37778931862957161709568)
  eFloor := (813374719273/151115727451828646838272)
}

#check "COMPACT_WITNESS_READY"
theorem checked : ComputedPolynomialCell.checks data witness=true := by decide +kernel
#check "COMPACT_CHECK_PASSED"

noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 12)
        (CoreQuotient.fused G u 9 12) ((51/26 : ℚ) : ℝ) y :=
  ComputedPolynomialCell.computed_actual_integral (51/26) 9 12 witness checked G u hd
#print axioms checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.CompactAnchor003Cell047
