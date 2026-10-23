/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell044
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (271413/1099511627776)
  b := (1194217/4398046511104)
  s := [(4398046494097/4398046511104),(-3401/4398046511104),(-85/2199023255552)]
  L := [(781359212339/295147905179352825856),(1875258647567/3541774862152233910272),(46881379109/1770887431076116955136),(-7/110680464442257309696),(1/110680464442257309696)]
  c := (781359212339/295147905179352825856)
  R := (-493742686451383/50000000000000)
  total := (-6064103/25000000000000)
  k := 29
  n := 32
  sFloor := (2199023245263/4398046511104)
  nFloor := (583911101047/151115727451828646838272)
  eFloor := (213222219883/75557863725914323419136)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell044
