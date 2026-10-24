/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode153
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e154 : NestedArithmetic.Expr 3 := .scaled -1 e153
noncomputable def p154 : NestedHorner.Poly 3 := [[[-1]],[[0]],[[-14]],[[0]],[[-81]],[[0]],[[-250]],[[0]],[[-444]],[[0]],[[-458]],[[0]],[[-265]],[[0]],[[-78]],[[0]],[[-9]]]
theorem step154 : p154=NestedHorner.scale -1 p153 := by decide +kernel
#print axioms step154
theorem h154 : NestedArithmetic.compile e154=p154 := by
  change NestedHorner.scale -1 (NestedArithmetic.compile e153)=p154
  rw [h153]
  exact step154.symm
#print axioms h154
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
