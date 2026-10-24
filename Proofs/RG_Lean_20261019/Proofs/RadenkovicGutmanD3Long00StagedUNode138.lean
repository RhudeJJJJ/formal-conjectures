/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode137
import Proofs.RadenkovicGutmanD3Long00StagedUNode003
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e138 : NestedArithmetic.Expr 3 := .times e137 e003
noncomputable def p138 : NestedHorner.Poly 3 := [[[]],[[0]],[[2]]]
theorem step138 : p138=NestedArithmetic.mul p137 p003 := by decide +kernel
#print axioms step138
theorem h138 : NestedArithmetic.compile e138=p138 := by
  change NestedArithmetic.mul (NestedArithmetic.compile e137) (NestedArithmetic.compile e003)=p138
  rw [h137,h003]
  exact step138.symm
#print axioms h138
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
