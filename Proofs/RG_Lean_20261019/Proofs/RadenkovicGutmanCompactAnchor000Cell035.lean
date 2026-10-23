/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell035
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (1841697/17592186044416)
  b := (1012933/8796093022208)
  s := [(2199023253817/2199023255552),(-695/4398046511104),(-17/2199023255552)]
  L := [(2491227895727/4722366482869645213696),(373682763743/3541774862152233910272),(37368134237/7083549724304467820544),(-5/885443715538058477568),(1/442721857769029238784)]
  c := (1245613947863/2361183241434822606848)
  R := (-213628001646463/20000000000000)
  total := (-55657321/500000000000000)
  k := 31
  n := 32
  sFloor := (549755813363/1099511627776)
  nFloor := (751881046085/1208925819614629174706176)
  eFloor := (562238953773/1208925819614629174706176)
}

#check "COMPACT_WITNESS_READY"
theorem checked : ComputedPolynomialCell.checks data witness=true := by decide +kernel
#check "COMPACT_CHECK_PASSED"

noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 9)
        (CoreQuotient.fused G u 9 9) ((51/26 : ℚ) : ℝ) y :=
  ComputedPolynomialCell.computed_actual_integral (51/26) 9 9 witness checked G u hd
#print axioms checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell035
