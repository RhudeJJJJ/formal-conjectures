/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode022
import Proofs.RadenkovicGutmanD3Long00StagedUNode144
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e145 : NestedArithmetic.Expr 3 := .times e022 e144
noncomputable def p145 : NestedHorner.Poly 3 := [[[],[]],[[],[0]],[[],[0]],[[],[0]],[[],[0]],[[],[0]],[[],[0]],[[],[0]],[[],[0]],[[],[0]],[[],[1]]]
theorem step145 : p145=NestedArithmetic.mul p022 p144 := by decide +kernel
#print axioms step145
theorem h145 : NestedArithmetic.compile e145=p145 := by
  change NestedArithmetic.mul (NestedArithmetic.compile e022) (NestedArithmetic.compile e144)=p145
  rw [h022,h144]
  exact step145.symm
#print axioms h145
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
