/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell145
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (2008831/536870912)
  b := (1104857/268435456)
  s := [(5310307984801/8796093022208),(-165500174739/4398046511104),(1905315115/1099511627776)]
  L := [(798743737105329709395/2361183241434822606848),(2114423852435/52776558133248),(-25283102167/26388279066624),(-124164893/3298534883328),(9215179/1649267441664)]
  c := (1487776147397/4398046511104)
  R := (-13548474763407/25000000000000)
  total := (-192280605961/1000000000000000)
  k := 2
  n := 32
  sFloor := (312159384765/1099511627776)
  nFloor := (1000746417193/1125899906842624)
  eFloor := (1462044662137/2251799813685248)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell145
