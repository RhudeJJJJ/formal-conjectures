/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell021
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (242489/8796093022208)
  b := (1066951/35184372088832)
  s := [(4398046511061/4398046511104),(-7/4398046511104),(-1/2199023255552)]
  L := [(6840822353956067934421191427/1361129467683753853853498429727072845824),(1822749961009/1813388729421943762059264),(45568467109/906694364710971881029632),(5/113336795588871485128704),(-1/56668397794435742564352)]
  c := (759483848473/151115727451828646838272)
  R := (-40650668766187/3125000000000)
  total := (-35727129/1000000000000000)
  k := 38
  n := 32
  sFloor := (1099511627763/2199023255552)
  nFloor := (1412480737943/38685626227668133590597632)
  eFloor := (1349225910765/38685626227668133590597632)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell021
