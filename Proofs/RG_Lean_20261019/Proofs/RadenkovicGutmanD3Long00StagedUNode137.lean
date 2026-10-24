/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode017
import Proofs.RadenkovicGutmanD3Long00StagedUNode118
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e137 : NestedArithmetic.Expr 3 := .times e017 e118
noncomputable def p137 : NestedHorner.Poly 3 := [[[2]]]
theorem step137 : p137=NestedArithmetic.mul p017 p118 := by decide +kernel
#print axioms step137
theorem h137 : NestedArithmetic.compile e137=p137 := by
  change NestedArithmetic.mul (NestedArithmetic.compile e017) (NestedArithmetic.compile e118)=p137
  rw [h017,h118]
  exact step137.symm
#print axioms h137
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
