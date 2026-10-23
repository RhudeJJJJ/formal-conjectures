/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell105
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (177543/2147483648)
  b := (781189/8589934592)
  s := [(274758756447/274877906944),(-381031721/4398046511104),(-9496707/2199023255552)]
  L := [(376273784370464128275897415/1267650600228229401496703205376),(1068957838233/18014398509481984),(26676540165/9007199254740992),(-590989/1125899906842624),(-7341/562949953421312)]
  c := (668396510353/2251799813685248)
  R := (-25382371236873/6250000000000)
  total := (-33175659339/1000000000000000)
  k := 12
  n := 32
  sFloor := (68683438719/137438953472)
  nFloor := (249857732351/576460752303423488)
  eFloor := (1459817446837/4611686018427387904)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell105
