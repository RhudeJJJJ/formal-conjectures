/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode002
import Proofs.RadenkovicGutmanD3Long00StagedUNode055
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e059 : NestedArithmetic.Expr 3 := .times e002 e055
noncomputable def p059 : NestedHorner.Poly 3 := [[[0],[0]],[[0,9],[9]],[[0,0],[0]],[[135,39],[39]],[[0,0],[0]],[[900,48],[48]],[[0,0],[0]],[[2337,21],[21]],[[0,0],[0]],[[3168,3],[3]],[[0]],[[2484]],[[0]],[[1164]],[[0]],[[321]],[[0]],[[48]],[[0]],[[3]]]
theorem step059 : p059=NestedArithmetic.mul p002 p055 := by decide +kernel
#print axioms step059
theorem h059 : NestedArithmetic.compile e059=p059 := by
  change NestedArithmetic.mul (NestedArithmetic.compile e002) (NestedArithmetic.compile e055)=p059
  rw [h002,h055]
  exact step059.symm
#print axioms h059
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
