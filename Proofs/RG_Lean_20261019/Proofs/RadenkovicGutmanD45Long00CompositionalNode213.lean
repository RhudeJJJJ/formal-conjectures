/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD45Long00CompositionalNode030
import Proofs.RadenkovicGutmanD45Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e213 : NestedArithmetic.Expr 3 := .times e030 e158
noncomputable def p213 : NestedHorner.Poly 3 := [[[45],[0]],[[0,0],[0]],[[675,0],[0,0]],[[0,0],[0,0]],[[4230,0],[0,0]],[[0,0],[0,0]],[[14355,0],[0,0]],[[0,0],[0,0]],[[28620,0],[0,0]],[[0,0],[0,0]],[[34020,45],[45,0]],[[0,0],[0,0]],[[23130,360],[360,0]],[[0,0],[0,0]],[[7515,990],[990,0]],[[0,0],[0,0]],[[135,1080],[1080,0]],[[0,0],[0,0]],[[-405,405],[405,0]],[[0],[0,0]],[[0],[0,45]]]
theorem step213 : p213=NestedArithmetic.mul p030 p158 := by decide +kernel
#print axioms step213
theorem h213 : NestedArithmetic.compile e213=p213 := StagedExprCompile.compile_times e213 e030 e158 p030 p158 p213 rfl h030 h158 step213
#print axioms h213
end Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
