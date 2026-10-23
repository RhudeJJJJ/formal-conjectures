/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor003Cell038
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 12
def witness : ComputedPolynomialCell.Witness := {
  a := (76603/549755813888)
  b := (337053/2199023255552)
  s := [(4398046510003/4398046511104),(-221/4398046511104),(-5/2199023255552)]
  L := [(695520223133832680955294367/5316911983139663491615228241121378304),(2965161697699/113336795588871485128704),(74128558579/56668397794435742564352),(-19/7083549724304467820544),(5/3541774862152233910272)]
  c := (154436513163/1180591620717411303424)
  R := (-568931342710019/50000000000000)
  total := (-157874319/1000000000000000)
  k := 33
  n := 32
  sFloor := (1099511627443/2199023255552)
  nFloor := (38233507191/37778931862957161709568)
  eFloor := (585175178547/604462909807314587353088)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor003Cell038
