/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode036
import Proofs.RadenkovicGutmanD3Long00StagedUNode215
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e216 : NestedArithmetic.Expr 3 := .times e036 e215
noncomputable def p216 : NestedHorner.Poly 3 := [[[3],[0]],[[0,0],[0]],[[48,0],[0]],[[0,0],[0]],[[321,0],[0]],[[0,0],[0]],[[1164,0],[0]],[[0,0],[0]],[[2484,0],[0]],[[0,0],[0]],[[3168,3],[3]],[[0,0],[0]],[[2337,21],[21]],[[0,0],[0]],[[900,48],[48]],[[0,0],[0]],[[135,39],[39]],[[0,0],[0]],[[0,9],[9]]]
theorem step216 : p216=NestedArithmetic.mul p036 p215 := by decide +kernel
#print axioms step216
theorem h216 : NestedArithmetic.compile e216=p216 := by
  change NestedArithmetic.mul (NestedArithmetic.compile e036) (NestedArithmetic.compile e215)=p216
  rw [h036,h215]
  exact step216.symm
#print axioms h216
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
