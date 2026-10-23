/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell056
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (851807/1099511627776)
  b := (936987/1099511627776)
  s := [(4398046343595/4398046511104),(-33503/4398046511104),(-837/2199023255552)]
  L := [(3848060084677/147573952589676412928),(2308816987391/442721857769029238784),(57719941295/221360928884514619392),(-49/13835058055282163712),(-5/13835058055282163712)]
  c := (962015021169/36893488147419103232)
  R := (-873113541719273/100000000000000)
  total := (-672657647/1000000000000000)
  k := 26
  n := 32
  sFloor := (2199023154209/4398046511104)
  nFloor := (718915526977/18889465931478580854784)
  eFloor := (262520723269/9444732965739290427392)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell056
