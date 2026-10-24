/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode175
import Proofs.RadenkovicGutmanD3Long00StagedUNode120
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e176 : NestedArithmetic.Expr 3 := .times e175 e120
noncomputable def p176 : NestedHorner.Poly 3 := [[[-2],[0]],[[0,0],[0]],[[-34,0],[0,0]],[[0,0],[0,0]],[[-244,0],[0,0]],[[0,0],[0,0]],[[-962,0],[0,0]],[[0,0],[0,0]],[[-2272,0],[0,0]],[[0,0],[0,0]],[[-3288,-2],[-2,0]],[[0,0],[0,0]],[[-2860,-16],[-16,0]],[[0,0],[0,0]],[[-1394,-44],[-44,0]],[[0,0],[0,0]],[[-318,-48],[-48,0]],[[0,0],[0,0]],[[-18,-18],[-18,0]],[[0],[0,0]],[[0],[0,-2]]]
theorem step176 : p176=NestedArithmetic.mul p175 p120 := by decide +kernel
#print axioms step176
theorem h176 : NestedArithmetic.compile e176=p176 := by
  change NestedArithmetic.mul (NestedArithmetic.compile e175) (NestedArithmetic.compile e120)=p176
  rw [h175,h120]
  exact step176.symm
#print axioms h176
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
