/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode137
import Proofs.RadenkovicGutmanD3Long00StagedUNode120
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e187 : NestedArithmetic.Expr 3 := .times e137 e120
noncomputable def p187 : NestedHorner.Poly 3 := [[[2]]]
theorem step187 : p187=NestedArithmetic.mul p137 p120 := by decide +kernel
#print axioms step187
theorem h187 : NestedArithmetic.compile e187=p187 := by
  change NestedArithmetic.mul (NestedArithmetic.compile e137) (NestedArithmetic.compile e120)=p187
  rw [h137,h120]
  exact step187.symm
#print axioms h187
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
