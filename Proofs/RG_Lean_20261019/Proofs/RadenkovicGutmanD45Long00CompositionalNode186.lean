/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD45Long00CompositionalNode178
import Proofs.RadenkovicGutmanD45Long00CompositionalNode185
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e186 : NestedArithmetic.Expr 3 := .plus e178 e185
noncomputable def p186 : NestedHorner.Poly 3 := [[[-86],[0]],[[0,0],[0]],[[-1417,0],[0,0]],[[0,0],[0,0]],[[-9772,0],[0,0]],[[0,0],[0,0]],[[-36551,0],[0,0]],[[0,0],[0,0]],[[-80236,0],[0,0]],[[0,0],[0,0]],[[-104124,-86],[-86,0]],[[0,0],[0,0]],[[-75460,-643],[-643,0]],[[0,0],[0,0]],[[-24887,-1577],[-1577,0]],[[0,0],[0,0]],[[-174,-1344],[-1344,0]],[[0,0],[0,0]],[[1251,-189],[-189,0]],[[0,0],[0,0]],[[0,135],[135,-86]]]
theorem step186 : p186=NestedHorner.add p178 p185 := by decide +kernel
#print axioms step186
theorem h186 : NestedArithmetic.compile e186=p186 := StagedExprCompile.compile_plus e186 e178 e185 p178 p185 p186 rfl h178 h185 step186
#print axioms h186
end Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
