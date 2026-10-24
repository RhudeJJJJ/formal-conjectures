/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode033
import Proofs.RadenkovicGutmanD3Long00StagedUNode028
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e034 : NestedArithmetic.Expr 3 := .times e033 e028
noncomputable def p034 : NestedHorner.Poly 3 := [[[0],[0]],[[0,-9],[-9]],[[0,0],[0]],[[-162,-39],[-39]],[[0,0],[0]],[[-1134,-48],[-48]],[[0,0],[0]],[[-3132,-21],[-21]],[[0,0],[0]],[[-4542,-3],[-3]],[[0]],[[-3816]],[[0]],[[-1914]],[[0]],[[-564]],[[0]],[[-90]],[[0]],[[-6]]]
theorem step034 : p034=NestedArithmetic.mul p033 p028 := by decide +kernel
#print axioms step034
theorem h034 : NestedArithmetic.compile e034=p034 := by
  change NestedArithmetic.mul (NestedArithmetic.compile e033) (NestedArithmetic.compile e028)=p034
  rw [h033,h028]
  exact step034.symm
#print axioms h034
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
