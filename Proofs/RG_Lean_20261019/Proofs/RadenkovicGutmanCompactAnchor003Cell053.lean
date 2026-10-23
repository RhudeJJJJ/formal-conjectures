/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor003Cell053
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 12
def witness : ComputedPolynomialCell.Witness := {
  a := (79997/137438953472)
  b := (1407947/2199023255552)
  s := [(4398046491897/4398046511104),(-3839/4398046511104),(-97/2199023255552)]
  L := [(5389590996647/2361183241434822606848),(3233749529569/7083549724304467820544),(26947870139/1180591620717411303424),(-31/442721857769029238784),(1/73786976294838206464)]
  c := (1347397749161/590295810358705651712)
  R := (-62181122511469/6250000000000)
  total := (-57626671/100000000000000)
  k := 29
  n := 32
  sFloor := (549755810983/1099511627776)
  nFloor := (1334289170631/75557863725914323419136)
  eFloor := (319088935751/18889465931478580854784)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor003Cell053
