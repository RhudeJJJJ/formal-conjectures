/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell226
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (552519/65536)
  b := (1215541/131072)
  s := [(3554553630539/4503599627370496),(-1015380306949/4503599627370496),(19580780859/562949953421312)]
  L := [(4841086523653620769763/4722366482869645213696),(-60867676705/13194139533312),(4091273117/6597069766656),(-58506185/824633720832),(2487823/412316860416)]
  c := (1122691489695/1099511627776)
  R := (521570294293/50000000000000)
  total := (9594916510463/1000000000000000)
  k := 0
  n := 32
  sFloor := (1347909785231/4503599627370496)
  nFloor := 1069718395797742830293513939307986731533336576
  eFloor := 1041839347640914217733865309283045090399354880
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell226
