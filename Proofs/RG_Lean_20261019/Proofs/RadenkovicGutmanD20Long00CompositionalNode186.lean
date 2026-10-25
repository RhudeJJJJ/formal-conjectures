/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD20Long00CompositionalNode178
import Proofs.RadenkovicGutmanD20Long00CompositionalNode185
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e186 : NestedArithmetic.Expr 3 := .plus e178 e185
noncomputable def p186 : NestedHorner.Poly 3 := [[[-36],[0]],[[0,0],[0]],[[-592,0],[0,0]],[[0,0],[0,0]],[[-4072,0],[0,0]],[[0,0],[0,0]],[[-15176,0],[0,0]],[[0,0],[0,0]],[[-33136,0],[0,0]],[[0,0],[0,0]],[[-42624,-36],[-36,0]],[[0,0],[0,0]],[[-30360,-268],[-268,0]],[[0,0],[0,0]],[[-9512,-652],[-652,0]],[[0,0],[0,0]],[[276,-544],[-544,0]],[[0,0],[0,0]],[[576,-64],[-64,0]],[[0,0],[0,0]],[[0,60],[60,-36]]]
theorem step186 : p186=NestedHorner.add p178 p185 := by decide +kernel
#print axioms step186
theorem h186 : NestedArithmetic.compile e186=p186 := StagedExprCompile.compile_plus e186 e178 e185 p178 p185 p186 rfl h178 h185 step186
#print axioms h186
end Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
