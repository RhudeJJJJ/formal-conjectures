/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor003Cell063
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 12
def witness : ComputedPolynomialCell.Witness := {
  a := (829963/549755813888)
  b := (912959/549755813888)
  s := [(549755797737/549755813888),(-25843/4398046511104),(-645/2199023255552)]
  L := [(637860466099264952877101759/41538374868278621028243970633760768),(56653183473/18446744073709551616),(33991782841/221360928884514619392),(-9/4611686018427387904),(-1/13835058055282163712)]
  c := (566533900769/36893488147419103232)
  R := (-112448524864283/12500000000000)
  total := (-13507901/10000000000000)
  k := 26
  n := 32
  sFloor := (2199023177381/4398046511104)
  nFloor := (561022214813/4722366482869645213696)
  eFloor := (536663222319/4722366482869645213696)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor003Cell063
