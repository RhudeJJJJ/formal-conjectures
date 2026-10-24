/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode154
import Proofs.RadenkovicGutmanD3Long00StagedUNode003
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e155 : NestedArithmetic.Expr 3 := .times e154 e003
noncomputable def p155 : NestedHorner.Poly 3 := [[[]],[[0]],[[-1]],[[0]],[[-14]],[[0]],[[-81]],[[0]],[[-250]],[[0]],[[-444]],[[0]],[[-458]],[[0]],[[-265]],[[0]],[[-78]],[[0]],[[-9]]]
theorem step155 : p155=NestedArithmetic.mul p154 p003 := by decide +kernel
#print axioms step155
theorem h155 : NestedArithmetic.compile e155=p155 := by
  change NestedArithmetic.mul (NestedArithmetic.compile e154) (NestedArithmetic.compile e003)=p155
  rw [h154,h003]
  exact step155.symm
#print axioms h155
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
