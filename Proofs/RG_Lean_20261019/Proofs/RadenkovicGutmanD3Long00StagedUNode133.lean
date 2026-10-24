/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode002
import Proofs.RadenkovicGutmanD3Long00StagedUNode001
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e133 : NestedArithmetic.Expr 3 := .times e002 e001
noncomputable def p133 : NestedHorner.Poly 3 := [[[]],[[0]],[[0]],[[0]],[[3]]]
theorem step133 : p133=NestedArithmetic.mul p002 p001 := by decide +kernel
#print axioms step133
theorem h133 : NestedArithmetic.compile e133=p133 := by
  change NestedArithmetic.mul (NestedArithmetic.compile e002) (NestedArithmetic.compile e001)=p133
  rw [h002,h001]
  exact step133.symm
#print axioms h133
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
