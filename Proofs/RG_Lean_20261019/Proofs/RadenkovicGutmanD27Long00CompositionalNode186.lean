/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD27Long00CompositionalNode178
import Proofs.RadenkovicGutmanD27Long00CompositionalNode185
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e186 : NestedArithmetic.Expr 3 := .plus e178 e185
noncomputable def p186 : NestedHorner.Poly 3 := [[[-50],[0]],[[0,0],[0]],[[-823,0],[0,0]],[[0,0],[0,0]],[[-5668,0],[0,0]],[[0,0],[0,0]],[[-21161,0],[0,0]],[[0,0],[0,0]],[[-46324,0],[0,0]],[[0,0],[0,0]],[[-59844,-50],[-50,0]],[[0,0],[0,0]],[[-42988,-373],[-373,0]],[[0,0],[0,0]],[[-13817,-911],[-911,0]],[[0,0],[0,0]],[[150,-768],[-768,0]],[[0,0],[0,0]],[[765,-99],[-99,0]],[[0,0],[0,0]],[[0,81],[81,-50]]]
theorem step186 : p186=NestedHorner.add p178 p185 := by decide +kernel
#print axioms step186
theorem h186 : NestedArithmetic.compile e186=p186 := StagedExprCompile.compile_plus e186 e178 e185 p178 p185 p186 rfl h178 h185 step186
#print axioms h186
end Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
