/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD21Long00CompositionalNode178
import Proofs.RadenkovicGutmanD21Long00CompositionalNode185
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e186 : NestedArithmetic.Expr 3 := .plus e178 e185
noncomputable def p186 : NestedHorner.Poly 3 := [[[-38],[0]],[[0,0],[0]],[[-625,0],[0,0]],[[0,0],[0,0]],[[-4300,0],[0,0]],[[0,0],[0,0]],[[-16031,0],[0,0]],[[0,0],[0,0]],[[-35020,0],[0,0]],[[0,0],[0,0]],[[-45084,-38],[-38,0]],[[0,0],[0,0]],[[-32164,-283],[-283,0]],[[0,0],[0,0]],[[-10127,-689],[-689,0]],[[0,0],[0,0]],[[258,-576],[-576,0]],[[0,0],[0,0]],[[603,-69],[-69,0]],[[0,0],[0,0]],[[0,63],[63,-38]]]
theorem step186 : p186=NestedHorner.add p178 p185 := by decide +kernel
#print axioms step186
theorem h186 : NestedArithmetic.compile e186=p186 := StagedExprCompile.compile_plus e186 e178 e185 p178 p185 p186 rfl h178 h185 step186
#print axioms h186
end Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
