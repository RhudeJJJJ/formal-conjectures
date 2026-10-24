/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode006
import Proofs.RadenkovicGutmanD3Long00StagedUNode001
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e126 : NestedArithmetic.Expr 3 := .times e006 e001
noncomputable def p126 : NestedHorner.Poly 3 := [[[]],[[0]],[[0]],[[0]],[[1]]]
theorem step126 : p126=NestedArithmetic.mul p006 p001 := by decide +kernel
#print axioms step126
theorem h126 : NestedArithmetic.compile e126=p126 := by
  change NestedArithmetic.mul (NestedArithmetic.compile e006) (NestedArithmetic.compile e001)=p126
  rw [h006,h001]
  exact step126.symm
#print axioms h126
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
