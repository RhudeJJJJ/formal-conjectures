/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode033
import Proofs.RadenkovicGutmanD3Long00StagedUNode181
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e215 : NestedArithmetic.Expr 3 := .times e033 e181
noncomputable def p215 : NestedHorner.Poly 3 := [[[-3],[0]],[[0,0],[0]],[[-48,0],[0]],[[0,0],[0]],[[-321,0],[0]],[[0,0],[0]],[[-1164,0],[0]],[[0,0],[0]],[[-2484,0],[0]],[[0,0],[0]],[[-3168,-3],[-3]],[[0,0],[0]],[[-2337,-21],[-21]],[[0,0],[0]],[[-900,-48],[-48]],[[0,0],[0]],[[-135,-39],[-39]],[[0,0],[0]],[[0,-9],[-9]]]
theorem step215 : p215=NestedArithmetic.mul p033 p181 := by decide +kernel
#print axioms step215
theorem h215 : NestedArithmetic.compile e215=p215 := by
  change NestedArithmetic.mul (NestedArithmetic.compile e033) (NestedArithmetic.compile e181)=p215
  rw [h033,h181]
  exact step215.symm
#print axioms h215
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
