/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor003Cell075
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 12
def witness : ComputedPolynomialCell.Witness := {
  a := (1302383/274877906944)
  b := (1432621/274877906944)
  s := [(2199022619229/2199023255552),(-254529/4398046511104),(-6363/2199023255552)]
  L := [(12565376991222135800107362747/83076749736557242056487941267521536),(837020057527/27670116110564327424),(20925426683/13835058055282163712),(-41/216172782113783808),(-5/864691128455135232)]
  c := (697518542437/4611686018427387904)
  R := (-785216513014449/100000000000000)
  total := (-3697445083/1000000000000000)
  k := 23
  n := 32
  sFloor := (2199022485601/4398046511104)
  nFloor := (1381465466985/1180591620717411303424)
  eFloor := (330370923521/295147905179352825856)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor003Cell075
