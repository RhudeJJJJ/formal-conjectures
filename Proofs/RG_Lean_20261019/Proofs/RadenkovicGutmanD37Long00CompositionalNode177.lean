/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD37Long00CompositionalNode174
import Proofs.RadenkovicGutmanD37Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e177 : NestedArithmetic.Expr 3 := .times e174 e176
noncomputable def p177 : NestedHorner.Poly 3 := [[[-70],[0]],[[0,0],[0]],[[-1190,0],[0,0]],[[0,0],[0,0]],[[-8540,0],[0,0]],[[0,0],[0,0]],[[-33670,0],[0,0]],[[0,0],[0,0]],[[-79520,0],[0,0]],[[0,0],[0,0]],[[-115080,-70],[-70,0]],[[0,0],[0,0]],[[-100100,-560],[-560,0]],[[0,0],[0,0]],[[-48790,-1540],[-1540,0]],[[0,0],[0,0]],[[-11130,-1680],[-1680,0]],[[0,0],[0,0]],[[-630,-630],[-630,0]],[[0],[0,0]],[[0],[0,-70]]]
theorem step177 : p177=NestedArithmetic.mul p174 p176 := by decide +kernel
#print axioms step177
theorem h177 : NestedArithmetic.compile e177=p177 := StagedExprCompile.compile_times e177 e174 e176 p174 p176 p177 rfl h174 h176 step177
#print axioms h177
end Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
