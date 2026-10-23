/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell053
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (79997/137438953472)
  b := (1407947/2199023255552)
  s := [(4398046492279/4398046511104),(-3767/4398046511104),(-93/2199023255552)]
  L := [(5290075015483/2361183241434822606848),(1058013344915/2361183241434822606848),(79350875365/3541774862152233910272),(-5/147573952589676412928),(-1/221360928884514619392)]
  c := (661259376935/295147905179352825856)
  R := (-497914906935947/50000000000000)
  total := (-576809099/1000000000000000)
  k := 29
  n := 32
  sFloor := (2199023244163/4398046511104)
  nFloor := (1229803818731/75557863725914323419136)
  eFloor := (73420610845/4722366482869645213696)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell053
