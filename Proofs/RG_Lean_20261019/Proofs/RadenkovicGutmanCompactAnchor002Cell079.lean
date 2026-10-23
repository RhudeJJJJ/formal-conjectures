/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell079
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (1906817/274877906944)
  b := (1048749/137438953472)
  s := [(4398033080631/4398046511104),(-335759/549755813888),(-33575/1099511627776)]
  L := [(5427701051844532141155362449/2596148429267413814265248164610048),(964146841347/2305843009213693952),(72309845311/3458764513820540928),(-3761/144115188075855872),(-139/216172782113783808)]
  c := (1205191735707/576460752303423488)
  R := (-653901193302703/100000000000000)
  total := (-1125622699/250000000000000)
  k := 19
  n := 32
  sFloor := (2199015130129/4398046511104)
  nFloor := (450322347027/147573952589676412928)
  eFloor := (657762665535/295147905179352825856)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell079
