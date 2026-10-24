/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode165
import Proofs.RadenkovicGutmanD3Long00StagedUNode167
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e168 : NestedArithmetic.Expr 3 := .plus e165 e167
noncomputable def p168 : NestedHorner.Poly 3 := [[[2],[]],[[0,0],[0]],[[30,0],[0]],[[0,0],[0]],[[188,0],[0]],[[0,0],[0]],[[638,0],[0]],[[0,0],[0]],[[1272,0],[0]],[[0,0],[0]],[[1514,1],[1]],[[0,0],[0]],[[1044,7],[7]],[[0,0],[0]],[[378,16],[16]],[[0,0],[0]],[[54,13],[13]],[[0,0],[0]],[[0,3],[3]]]
theorem step168 : p168=NestedHorner.add p165 p167 := by decide +kernel
#print axioms step168
theorem h168 : NestedArithmetic.compile e168=p168 := by
  change NestedHorner.add (NestedArithmetic.compile e165) (NestedArithmetic.compile e167)=p168
  rw [h165,h167]
  exact step168.symm
#print axioms h168
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
