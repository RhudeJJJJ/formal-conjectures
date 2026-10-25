/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD37Long00CompositionalNode177
import Proofs.RadenkovicGutmanD37Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e178 : NestedArithmetic.Expr 3 := .times e177 e122
noncomputable def p178 : NestedHorner.Poly 3 := [[[-70],[0]],[[0,0],[0]],[[-1190,0],[0,0]],[[0,0],[0,0]],[[-8540,0],[0,0]],[[0,0],[0,0]],[[-33670,0],[0,0]],[[0,0],[0,0]],[[-79520,0],[0,0]],[[0,0],[0,0]],[[-115080,-70],[-70,0]],[[0,0],[0,0]],[[-100100,-560],[-560,0]],[[0,0],[0,0]],[[-48790,-1540],[-1540,0]],[[0,0],[0,0]],[[-11130,-1680],[-1680,0]],[[0,0],[0,0]],[[-630,-630],[-630,0]],[[0],[0,0]],[[0],[0,-70]]]
theorem step178 : p178=NestedArithmetic.mul p177 p122 := by decide +kernel
#print axioms step178
theorem h178 : NestedArithmetic.compile e178=p178 := StagedExprCompile.compile_times e178 e177 e122 p177 p122 p178 rfl h177 h122 step178
#print axioms h178
end Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
