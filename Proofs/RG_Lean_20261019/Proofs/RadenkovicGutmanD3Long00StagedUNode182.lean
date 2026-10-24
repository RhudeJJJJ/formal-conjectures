/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode002
import Proofs.RadenkovicGutmanD3Long00StagedUNode181
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e182 : NestedArithmetic.Expr 3 := .times e002 e181
noncomputable def p182 : NestedHorner.Poly 3 := [[[3],[0]],[[0,0],[0]],[[48,0],[0]],[[0,0],[0]],[[321,0],[0]],[[0,0],[0]],[[1164,0],[0]],[[0,0],[0]],[[2484,0],[0]],[[0,0],[0]],[[3168,3],[3]],[[0,0],[0]],[[2337,21],[21]],[[0,0],[0]],[[900,48],[48]],[[0,0],[0]],[[135,39],[39]],[[0,0],[0]],[[0,9],[9]]]
theorem step182 : p182=NestedArithmetic.mul p002 p181 := by decide +kernel
#print axioms step182
theorem h182 : NestedArithmetic.compile e182=p182 := StagedExprCompile.compile_times e182 e002 e181 p002 p181 p182 rfl h002 h181 step182
#print axioms h182
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
