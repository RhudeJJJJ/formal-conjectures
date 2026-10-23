/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell068
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (334165/137438953472)
  b := (735163/274877906944)
  s := [(4398046182631/4398046511104),(-65693/4398046511104),(-1643/2199023255552)]
  L := [(2884604909841/73786976294838206464),(576920934645/73786976294838206464),(21634527943/55340232221128654848),(-59/4611686018427387904),(-1/3458764513820540928)]
  c := (180287806865/4611686018427387904)
  R := (-426432621419377/50000000000000)
  total := (-128866371/62500000000000)
  k := 25
  n := 32
  sFloor := (1099511528413/2199023255552)
  nFloor := (1341190209777/4722366482869645213696)
  eFloor := (1281127971231/4722366482869645213696)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell068
