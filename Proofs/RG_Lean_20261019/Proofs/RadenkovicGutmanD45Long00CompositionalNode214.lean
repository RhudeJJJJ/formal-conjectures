/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD45Long00CompositionalNode030
import Proofs.RadenkovicGutmanD45Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e214 : NestedArithmetic.Expr 3 := .times e030 e176
noncomputable def p214 : NestedHorner.Poly 3 := [[[45],[0]],[[0,0],[0]],[[765,0],[0,0]],[[0,0],[0,0]],[[5490,0],[0,0]],[[0,0],[0,0]],[[21645,0],[0,0]],[[0,0],[0,0]],[[51120,0],[0,0]],[[0,0],[0,0]],[[73980,45],[45,0]],[[0,0],[0,0]],[[64350,360],[360,0]],[[0,0],[0,0]],[[31365,990],[990,0]],[[0,0],[0,0]],[[7155,1080],[1080,0]],[[0,0],[0,0]],[[405,405],[405,0]],[[0],[0,0]],[[0],[0,45]]]
theorem step214 : p214=NestedArithmetic.mul p030 p176 := by decide +kernel
#print axioms step214
theorem h214 : NestedArithmetic.compile e214=p214 := StagedExprCompile.compile_times e214 e030 e176 p030 p176 p214 rfl h030 h176 step214
#print axioms h214
end Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
