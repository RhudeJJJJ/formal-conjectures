/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode128
import Proofs.RadenkovicGutmanD3Long00StagedUNode134
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e135 : NestedArithmetic.Expr 3 := .times e128 e134
noncomputable def p135 : NestedHorner.Poly 3 := [[[1]],[[0]],[[7]],[[0]],[[16]],[[0]],[[13]],[[0]],[[3]]]
theorem step135 : p135=NestedArithmetic.mul p128 p134 := by decide +kernel
#print axioms step135
theorem h135 : NestedArithmetic.compile e135=p135 := by
  change NestedArithmetic.mul (NestedArithmetic.compile e128) (NestedArithmetic.compile e134)=p135
  rw [h128,h134]
  exact step135.symm
#print axioms h135
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
