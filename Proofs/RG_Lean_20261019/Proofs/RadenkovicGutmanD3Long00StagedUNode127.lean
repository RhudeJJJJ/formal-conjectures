/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode125
import Proofs.RadenkovicGutmanD3Long00StagedUNode126
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e127 : NestedArithmetic.Expr 3 := .plus e125 e126
noncomputable def p127 : NestedHorner.Poly 3 := [[[1]],[[0]],[[3]],[[0]],[[1]]]
theorem step127 : p127=NestedHorner.add p125 p126 := by decide +kernel
#print axioms step127
theorem h127 : NestedArithmetic.compile e127=p127 := by
  change NestedHorner.add (NestedArithmetic.compile e125) (NestedArithmetic.compile e126)=p127
  rw [h125,h126]
  exact step127.symm
#print axioms h127
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
