/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell191
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (157289/524288)
  b := (1384143/4194304)
  s := [(4393859000829/17592186044416),(-115301832087/17592186044416),(-5195762531/8796093022208)]
  L := [(113288879723339837389/147573952589676412928),(530763095873/26388279066624),(6016651421/4398046511104),(-410735075/1649267441664),(5363343/274877906944)]
  c := (1688135858227/2199023255552)
  R := (-13219420468127/100000000000000)
  total := (-1881726583019/500000000000000)
  k := 1
  n := 32
  sFloor := (133380176365/1099511627776)
  nFloor := (1044005140421/2147483648)
  eFloor := (1632776830761/4294967296)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell191
