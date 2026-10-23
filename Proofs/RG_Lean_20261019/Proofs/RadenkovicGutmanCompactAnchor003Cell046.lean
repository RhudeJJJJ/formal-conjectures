/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor003Cell046
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 12
def witness : ComputedPolynomialCell.Witness := {
  a := (656819/2199023255552)
  b := (1445001/4398046511104)
  s := [(2199023253023/2199023255552),(-505/2199023255552),(-13/1099511627776)]
  L := [(3195873916184369014256565571/5316911983139663491615228241121378304),(851546686349/7083549724304467820544),(42577074781/7083549724304467820544),(1/442721857769029238784),(-1/442721857769029238784)]
  c := (709626561109/1180591620717411303424)
  R := (-212322979408543/20000000000000)
  total := (-315642507/1000000000000000)
  k := 31
  n := 32
  sFloor := (549755813123/1099511627776)
  nFloor := (1405445471325/302231454903657293676544)
  eFloor := (1344422512221/302231454903657293676544)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor003Cell046
