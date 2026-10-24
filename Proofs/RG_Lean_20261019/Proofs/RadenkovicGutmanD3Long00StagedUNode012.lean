/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode011
import Proofs.RadenkovicGutmanD3Long00StagedUNode002
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e012 : NestedArithmetic.Expr 3 := .plus e011 e002
noncomputable def p012 : NestedHorner.Poly 3 := [[[3]],[[0]],[[4]],[[0]],[[1]]]
theorem step012 : p012=NestedHorner.add p011 p002 := by decide +kernel
#print axioms step012
theorem h012 : NestedArithmetic.compile e012=p012 := by
  change NestedHorner.add (NestedArithmetic.compile e011) (NestedArithmetic.compile e002)=p012
  rw [h011,h002]
  exact step012.symm
#print axioms h012
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
