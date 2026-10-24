/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode118
import Proofs.RadenkovicGutmanD3Long00StagedUNode127
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e128 : NestedArithmetic.Expr 3 := .times e118 e127
noncomputable def p128 : NestedHorner.Poly 3 := [[[1]],[[0]],[[3]],[[0]],[[1]]]
theorem step128 : p128=NestedArithmetic.mul p118 p127 := by decide +kernel
#print axioms step128
theorem h128 : NestedArithmetic.compile e128=p128 := by
  change NestedArithmetic.mul (NestedArithmetic.compile e118) (NestedArithmetic.compile e127)=p128
  rw [h118,h127]
  exact step128.symm
#print axioms h128
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
