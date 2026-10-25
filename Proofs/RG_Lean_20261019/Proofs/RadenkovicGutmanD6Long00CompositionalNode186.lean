/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD6Long00CompositionalNode178
import Proofs.RadenkovicGutmanD6Long00CompositionalNode185
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e186 : NestedArithmetic.Expr 3 := .plus e178 e185
noncomputable def p186 : NestedHorner.Poly 3 := [[[-8],[0]],[[0,0],[0]],[[-130,0],[0,0]],[[0,0],[0,0]],[[-880,0],[0,0]],[[0,0],[0,0]],[[-3206,0],[0,0]],[[0,0],[0,0]],[[-6760,0],[0,0]],[[0,0],[0,0]],[[-8184,-8],[-8,0]],[[0,0],[0,0]],[[-5104,-58],[-58,0]],[[0,0],[0,0]],[[-902,-134],[-134,0]],[[0,0],[0,0]],[[528,-96],[-96,0]],[[0,0],[0,0]],[[198,6],[6,0]],[[0,0],[0,0]],[[0,18],[18,-8]]]
theorem step186 : p186=NestedHorner.add p178 p185 := by decide +kernel
#print axioms step186
theorem h186 : NestedArithmetic.compile e186=p186 := StagedExprCompile.compile_plus e186 e178 e185 p178 p185 p186 rfl h178 h185 step186
#print axioms h186
end Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
