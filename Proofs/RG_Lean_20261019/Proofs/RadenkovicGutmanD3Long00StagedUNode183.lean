/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode182
import Proofs.RadenkovicGutmanD3Long00StagedUNode003
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e183 : NestedArithmetic.Expr 3 := .times e182 e003
noncomputable def p183 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[3,0],[0]],[[0,0],[0]],[[48,0],[0]],[[0,0],[0]],[[321,0],[0]],[[0,0],[0]],[[1164,0],[0]],[[0,0],[0]],[[2484,0],[0]],[[0,0],[0]],[[3168,3],[3]],[[0,0],[0]],[[2337,21],[21]],[[0,0],[0]],[[900,48],[48]],[[0,0],[0]],[[135,39],[39]],[[0,0],[0]],[[0,9],[9]]]
theorem step183 : p183=NestedArithmetic.mul p182 p003 := by decide +kernel
#print axioms step183
theorem h183 : NestedArithmetic.compile e183=p183 := by
  change NestedArithmetic.mul (NestedArithmetic.compile e182) (NestedArithmetic.compile e003)=p183
  rw [h182,h003]
  exact step183.symm
#print axioms h183
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
