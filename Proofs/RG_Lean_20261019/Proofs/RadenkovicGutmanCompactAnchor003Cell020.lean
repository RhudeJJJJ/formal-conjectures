/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor003Cell020
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 12
def witness : ComputedPolynomialCell.Witness := {
  a := (881779/35184372088832)
  b := (242489/8796093022208)
  s := [(1099511627767/1099511627776),(-1/549755813888)]
  L := [(5115851662647/1208925819614629174706176),(3069479668141/3626777458843887524118528),(76736208559/1813388729421943762059264),(-19/226673591177742970257408),(5/113336795588871485128704)]
  c := (1278962915661/302231454903657293676544)
  R := (-40919389750567/3125000000000)
  total := (-32694613/1000000000000000)
  k := 38
  n := 32
  sFloor := (1099511627765/2199023255552)
  nFloor := (316630030155/9671406556917033397649408)
  eFloor := (302882288407/9671406556917033397649408)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor003Cell020
