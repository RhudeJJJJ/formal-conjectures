/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode024
import Proofs.RadenkovicGutmanD3Long00StagedUNode027
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e028 : NestedArithmetic.Expr 3 := .plus e024 e027
noncomputable def p028 : NestedHorner.Poly 3 := [[[],[]],[[0,3],[3]],[[0,0],[0]],[[54,13],[13]],[[0,0],[0]],[[378,16],[16]],[[0,0],[0]],[[1044,7],[7]],[[0,0],[0]],[[1514,1],[1]],[[0]],[[1272]],[[0]],[[638]],[[0]],[[188]],[[0]],[[30]],[[0]],[[2]]]
theorem step028 : p028=NestedHorner.add p024 p027 := by decide +kernel
#print axioms step028
theorem h028 : NestedArithmetic.compile e028=p028 := by
  change NestedHorner.add (NestedArithmetic.compile e024) (NestedArithmetic.compile e027)=p028
  rw [h024,h027]
  exact step028.symm
#print axioms h028
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
