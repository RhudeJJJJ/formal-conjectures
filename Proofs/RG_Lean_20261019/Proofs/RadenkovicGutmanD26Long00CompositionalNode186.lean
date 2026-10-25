/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD26Long00CompositionalNode178
import Proofs.RadenkovicGutmanD26Long00CompositionalNode185
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e186 : NestedArithmetic.Expr 3 := .plus e178 e185
noncomputable def p186 : NestedHorner.Poly 3 := [[[-48],[0]],[[0,0],[0]],[[-790,0],[0,0]],[[0,0],[0,0]],[[-5440,0],[0,0]],[[0,0],[0,0]],[[-20306,0],[0,0]],[[0,0],[0,0]],[[-44440,0],[0,0]],[[0,0],[0,0]],[[-57384,-48],[-48,0]],[[0,0],[0,0]],[[-41184,-358],[-358,0]],[[0,0],[0,0]],[[-13202,-874],[-874,0]],[[0,0],[0,0]],[[168,-736],[-736,0]],[[0,0],[0,0]],[[738,-94],[-94,0]],[[0,0],[0,0]],[[0,78],[78,-48]]]
theorem step186 : p186=NestedHorner.add p178 p185 := by decide +kernel
#print axioms step186
theorem h186 : NestedArithmetic.compile e186=p186 := StagedExprCompile.compile_plus e186 e178 e185 p178 p185 p186 rfl h178 h185 step186
#print axioms h186
end Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
