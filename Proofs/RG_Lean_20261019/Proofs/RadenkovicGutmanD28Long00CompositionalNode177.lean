/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD28Long00CompositionalNode174
import Proofs.RadenkovicGutmanD28Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e177 : NestedArithmetic.Expr 3 := .times e174 e176
noncomputable def p177 : NestedHorner.Poly 3 := [[[-52],[0]],[[0,0],[0]],[[-884,0],[0,0]],[[0,0],[0,0]],[[-6344,0],[0,0]],[[0,0],[0,0]],[[-25012,0],[0,0]],[[0,0],[0,0]],[[-59072,0],[0,0]],[[0,0],[0,0]],[[-85488,-52],[-52,0]],[[0,0],[0,0]],[[-74360,-416],[-416,0]],[[0,0],[0,0]],[[-36244,-1144],[-1144,0]],[[0,0],[0,0]],[[-8268,-1248],[-1248,0]],[[0,0],[0,0]],[[-468,-468],[-468,0]],[[0],[0,0]],[[0],[0,-52]]]
theorem step177 : p177=NestedArithmetic.mul p174 p176 := by decide +kernel
#print axioms step177
theorem h177 : NestedArithmetic.compile e177=p177 := StagedExprCompile.compile_times e177 e174 e176 p174 p176 p177 rfl h174 h176 step177
#print axioms h177
end Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
