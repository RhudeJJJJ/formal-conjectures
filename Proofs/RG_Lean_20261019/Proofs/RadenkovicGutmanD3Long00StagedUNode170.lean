/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode169
import Proofs.RadenkovicGutmanD3Long00StagedUNode003
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e170 : NestedArithmetic.Expr 3 := .times e169 e003
noncomputable def p170 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[6,0],[0]],[[0,0],[0]],[[90,0],[0]],[[0,0],[0]],[[564,0],[0]],[[0,0],[0]],[[1914,0],[0]],[[0,0],[0]],[[3816,0],[0]],[[0,0],[0]],[[4542,3],[3]],[[0,0],[0]],[[3132,21],[21]],[[0,0],[0]],[[1134,48],[48]],[[0,0],[0]],[[162,39],[39]],[[0,0],[0]],[[0,9],[9]]]
theorem step170 : p170=NestedArithmetic.mul p169 p003 := by decide +kernel
#print axioms step170
theorem h170 : NestedArithmetic.compile e170=p170 := by
  change NestedArithmetic.mul (NestedArithmetic.compile e169) (NestedArithmetic.compile e003)=p170
  rw [h169,h003]
  exact step170.symm
#print axioms h170
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
