/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell047
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (1445001/4398046511104)
  b := (1589501/4398046511104)
  s := [(4398046480975/4398046511104),(-3013/2199023255552),(-75/1099511627776)]
  L := [(24351491509860714904491329/5192296858534827628530496329220096),(276844212835/295147905179352825856),(13842200655/295147905179352825856),(-1/36893488147419103232),(-1/18446744073709551616)]
  c := (346055507945/73786976294838206464)
  R := (-479446222255817/50000000000000)
  total := (-15672923/50000000000000)
  k := 28
  n := 32
  sFloor := (549755809331/1099511627776)
  nFloor := (1034431539775/151115727451828646838272)
  eFloor := (1510940886943/302231454903657293676544)
}

#check "COMPACT_WITNESS_READY"
theorem checked : ComputedPolynomialCell.checks data witness=true := by decide +kernel
#check "COMPACT_CHECK_PASSED"

noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 11)
        (CoreQuotient.fused G u 9 11) ((51/26 : ℚ) : ℝ) y :=
  ComputedPolynomialCell.computed_actual_integral (51/26) 9 11 witness checked G u hd
#print axioms checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell047
