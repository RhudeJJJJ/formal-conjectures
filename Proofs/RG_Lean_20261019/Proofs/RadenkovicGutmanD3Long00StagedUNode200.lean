/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode199
import Proofs.RadenkovicGutmanD3Long00StagedUNode120
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e200 : NestedArithmetic.Expr 3 := .times e199 e120
noncomputable def p200 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[37,0],[0,0]],[[0,0],[0,0]],[[295,0],[0,0]],[[0,0],[0,0]],[[1328,0],[0,0]],[[0,0],[0,0]],[[3715,0],[0,0]],[[0,0],[0,0]],[[6696,2],[2,0]],[[0,0],[0,0]],[[7792,19],[19,0]],[[0,0],[0,0]],[[5684,68],[68,0]],[[0,0],[0,0]],[[2409,114],[114,0]],[[0,0],[0,0]],[[495,90],[90,0]],[[0,0],[0,0]],[[27,27],[27,2]],[[0],[0,0]],[[0],[0,3]]]
theorem step200 : p200=NestedArithmetic.mul p199 p120 := by decide +kernel
#print axioms step200
theorem h200 : NestedArithmetic.compile e200=p200 := by
  change NestedArithmetic.mul (NestedArithmetic.compile e199) (NestedArithmetic.compile e120)=p200
  rw [h199,h120]
  exact step200.symm
#print axioms h200
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
