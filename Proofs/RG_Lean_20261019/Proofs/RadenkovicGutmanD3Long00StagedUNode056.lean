/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode033
import Proofs.RadenkovicGutmanD3Long00StagedUNode055
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e056 : NestedArithmetic.Expr 3 := .times e033 e055
noncomputable def p056 : NestedHorner.Poly 3 := [[[0],[0]],[[0,-9],[-9]],[[0,0],[0]],[[-135,-39],[-39]],[[0,0],[0]],[[-900,-48],[-48]],[[0,0],[0]],[[-2337,-21],[-21]],[[0,0],[0]],[[-3168,-3],[-3]],[[0]],[[-2484]],[[0]],[[-1164]],[[0]],[[-321]],[[0]],[[-48]],[[0]],[[-3]]]
theorem step056 : p056=NestedArithmetic.mul p033 p055 := by decide +kernel
#print axioms step056
theorem h056 : NestedArithmetic.compile e056=p056 := by
  change NestedArithmetic.mul (NestedArithmetic.compile e033) (NestedArithmetic.compile e055)=p056
  rw [h033,h055]
  exact step056.symm
#print axioms h056
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
