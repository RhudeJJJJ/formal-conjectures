/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD12Long00CompositionalNode178
import Proofs.RadenkovicGutmanD12Long00CompositionalNode185
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e186 : NestedArithmetic.Expr 3 := .plus e178 e185
noncomputable def p186 : NestedHorner.Poly 3 := [[[-20],[0]],[[0,0],[0]],[[-328,0],[0,0]],[[0,0],[0,0]],[[-2248,0],[0,0]],[[0,0],[0,0]],[[-8336,0],[0,0]],[[0,0],[0,0]],[[-18064,0],[0,0]],[[0,0],[0,0]],[[-22944,-20],[-20,0]],[[0,0],[0,0]],[[-15928,-148],[-148,0]],[[0,0],[0,0]],[[-4592,-356],[-356,0]],[[0,0],[0,0]],[[420,-288],[-288,0]],[[0,0],[0,0]],[[360,-24],[-24,0]],[[0,0],[0,0]],[[0,36],[36,-20]]]
theorem step186 : p186=NestedHorner.add p178 p185 := by decide +kernel
#print axioms step186
theorem h186 : NestedArithmetic.compile e186=p186 := StagedExprCompile.compile_plus e186 e178 e185 p178 p185 p186 rfl h178 h185 step186
#print axioms h186
end Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
