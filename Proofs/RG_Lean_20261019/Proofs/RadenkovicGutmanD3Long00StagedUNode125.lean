/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode124
import Proofs.RadenkovicGutmanD3Long00StagedUNode120
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e125 : NestedArithmetic.Expr 3 := .times e124 e120
noncomputable def p125 : NestedHorner.Poly 3 := [[[1]],[[0]],[[3]]]
theorem step125 : p125=NestedArithmetic.mul p124 p120 := by decide +kernel
#print axioms step125
theorem h125 : NestedArithmetic.compile e125=p125 := by
  change NestedArithmetic.mul (NestedArithmetic.compile e124) (NestedArithmetic.compile e120)=p125
  rw [h124,h120]
  exact step125.symm
#print axioms h125
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
