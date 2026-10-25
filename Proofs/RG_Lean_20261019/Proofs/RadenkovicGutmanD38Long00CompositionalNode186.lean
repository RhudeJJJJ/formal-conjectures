/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD38Long00CompositionalNode178
import Proofs.RadenkovicGutmanD38Long00CompositionalNode185
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e186 : NestedArithmetic.Expr 3 := .plus e178 e185
noncomputable def p186 : NestedHorner.Poly 3 := [[[-72],[0]],[[0,0],[0]],[[-1186,0],[0,0]],[[0,0],[0,0]],[[-8176,0],[0,0]],[[0,0],[0,0]],[[-30566,0],[0,0]],[[0,0],[0,0]],[[-67048,0],[0,0]],[[0,0],[0,0]],[[-86904,-72],[-72,0]],[[0,0],[0,0]],[[-62832,-538],[-538,0]],[[0,0],[0,0]],[[-20582,-1318],[-1318,0]],[[0,0],[0,0]],[[-48,-1120],[-1120,0]],[[0,0],[0,0]],[[1062,-154],[-154,0]],[[0,0],[0,0]],[[0,114],[114,-72]]]
theorem step186 : p186=NestedHorner.add p178 p185 := by decide +kernel
#print axioms step186
theorem h186 : NestedArithmetic.compile e186=p186 := StagedExprCompile.compile_plus e186 e178 e185 p178 p185 p186 rfl h178 h185 step186
#print axioms h186
end Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
