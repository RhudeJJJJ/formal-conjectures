/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor004Cell020
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 13
def witness : ComputedPolynomialCell.Witness := {
  a := (881779/35184372088832)
  b := (242489/8796093022208)
  s := [(2199023255471/2199023255552),(-15/2199023255552),(-1/1099511627776)]
  L := [(3864661950215/151115727451828646838272),(386462250485/75557863725914323419136),(28984372955/113336795588871485128704),(-1/4722366482869645213696),(1/7083549724304467820544)]
  c := (1932330975107/75557863725914323419136)
  R := (-609735939333551/50000000000000)
  total := (-15220187/500000000000000)
  k := 36
  n := 32
  sFloor := (1099511627727/2199023255552)
  nFloor := (850882916801/19342813113834066795298816)
  eFloor := (1219588845265/38685626227668133590597632)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor004Cell020
