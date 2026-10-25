/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD42Long00CompositionalNode178
import Proofs.RadenkovicGutmanD42Long00CompositionalNode185
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e186 : NestedArithmetic.Expr 3 := .plus e178 e185
noncomputable def p186 : NestedHorner.Poly 3 := [[[-80],[0]],[[0,0],[0]],[[-1318,0],[0,0]],[[0,0],[0,0]],[[-9088,0],[0,0]],[[0,0],[0,0]],[[-33986,0],[0,0]],[[0,0],[0,0]],[[-74584,0],[0,0]],[[0,0],[0,0]],[[-96744,-80],[-80,0]],[[0,0],[0,0]],[[-70048,-598],[-598,0]],[[0,0],[0,0]],[[-23042,-1466],[-1466,0]],[[0,0],[0,0]],[[-120,-1248],[-1248,0]],[[0,0],[0,0]],[[1170,-174],[-174,0]],[[0,0],[0,0]],[[0,126],[126,-80]]]
theorem step186 : p186=NestedHorner.add p178 p185 := by decide +kernel
#print axioms step186
theorem h186 : NestedArithmetic.compile e186=p186 := StagedExprCompile.compile_plus e186 e178 e185 p178 p185 p186 rfl h178 h185 step186
#print axioms h186
end Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
