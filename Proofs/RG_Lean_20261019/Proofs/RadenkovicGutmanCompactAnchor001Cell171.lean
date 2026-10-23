/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell171
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (748167/16777216)
  b := (1645967/33554432)
  s := [(5070119034101/17592186044416),(-3423956429/4398046511104),(3266496839/4398046511104)]
  L := [(2774920589622134825153/4722366482869645213696),(24366698857/8796093022208),(-14576942761/13194139533312),(84502563/549755813888),(-9707951/824633720832)]
  c := (323043273485/549755813888)
  R := (-5316879170047/20000000000000)
  total := (-1181516685903/1000000000000000)
  k := 1
  n := 32
  sFloor := (632908890155/4398046511104)
  nFloor := (504265687715/4398046511104)
  eFloor := (474177001211/4398046511104)
}

#check "COMPACT_WITNESS_READY"
theorem checked : ComputedPolynomialCell.checks data witness=true := by decide +kernel
#check "COMPACT_CHECK_PASSED"

noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 10)
        (CoreQuotient.fused G u 9 10) ((51/26 : ℚ) : ℝ) y :=
  ComputedPolynomialCell.computed_actual_integral (51/26) 9 10 witness checked G u hd
#print axioms checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell171
