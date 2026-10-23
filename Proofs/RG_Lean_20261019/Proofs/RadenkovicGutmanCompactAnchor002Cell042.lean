/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell042
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (448617/2199023255552)
  b := (986957/4398046511104)
  s := [(137438953109/137438953472),(-581/1099511627776),(-29/1099511627776)]
  L := [(2134719907839/1180591620717411303424),(426942077041/1180591620717411303424),(32020512655/1770887431076116955136),0,(-1/110680464442257309696)]
  c := (2134719907839/1180591620717411303424)
  R := (-1006547303795051/100000000000000)
  total := (-204354661/1000000000000000)
  k := 30
  n := 32
  sFloor := (549755812131/1099511627776)
  nFloor := (3115781065/1180591620717411303424)
  eFloor := (145633951011/75557863725914323419136)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell042
