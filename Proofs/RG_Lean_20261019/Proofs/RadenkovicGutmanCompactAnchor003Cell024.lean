/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor003Cell024
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 12
def witness : ComputedPolynomialCell.Witness := {
  a := (645505/17592186044416)
  b := (1420111/35184372088832)
  s := [(4398046511027/4398046511104),(-1/274877906944)]
  L := [(48230023153798844730565973/5316911983139663491615228241121378304),(137077970389/75557863725914323419136),(20561695523/226673591177742970257408),(5/18889465931478580854784),(-1/7083549724304467820544)]
  c := (685389851949/75557863725914323419136)
  R := (-317824151028821/25000000000000)
  total := (-5808713/125000000000000)
  k := 37
  n := 32
  sFloor := (2199023255505/4398046511104)
  nFloor := (1357443640221/19342813113834066795298816)
  eFloor := (1298504869965/19342813113834066795298816)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor003Cell024
