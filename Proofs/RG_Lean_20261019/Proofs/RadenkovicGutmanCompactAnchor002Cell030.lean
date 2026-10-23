/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell030
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (571775/8796093022208)
  b := (1257905/17592186044416)
  s := [(1099511627481/1099511627776),(-237/4398046511104),(-5/2199023255552)]
  L := [(866921515333/4722366482869645213696),(1040305818109/28334198897217871282176),(1083651893/590295810358705651712),(-1/1770887431076116955136)]
  c := (866921515333/4722366482869645213696)
  R := (-1120919135755039/100000000000000)
  total := (-72548777/1000000000000000)
  k := 33
  n := 32
  sFloor := (1099511627419/2199023255552)
  nFloor := (323925978399/1208925819614629174706176)
  eFloor := (118285499399/604462909807314587353088)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell030
