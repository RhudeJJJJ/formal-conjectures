/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode033
import Proofs.RadenkovicGutmanD3Long00StagedUNode168
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e214 : NestedArithmetic.Expr 3 := .times e033 e168
noncomputable def p214 : NestedHorner.Poly 3 := [[[-6],[0]],[[0,0],[0]],[[-90,0],[0]],[[0,0],[0]],[[-564,0],[0]],[[0,0],[0]],[[-1914,0],[0]],[[0,0],[0]],[[-3816,0],[0]],[[0,0],[0]],[[-4542,-3],[-3]],[[0,0],[0]],[[-3132,-21],[-21]],[[0,0],[0]],[[-1134,-48],[-48]],[[0,0],[0]],[[-162,-39],[-39]],[[0,0],[0]],[[0,-9],[-9]]]
theorem step214 : p214=NestedArithmetic.mul p033 p168 := by decide +kernel
#print axioms step214
theorem h214 : NestedArithmetic.compile e214=p214 := by
  change NestedArithmetic.mul (NestedArithmetic.compile e033) (NestedArithmetic.compile e168)=p214
  rw [h033,h168]
  exact step214.symm
#print axioms h214
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
