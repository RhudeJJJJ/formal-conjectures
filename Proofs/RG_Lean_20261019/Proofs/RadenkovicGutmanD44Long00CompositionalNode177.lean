/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD44Long00CompositionalNode174
import Proofs.RadenkovicGutmanD44Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e177 : NestedArithmetic.Expr 3 := .times e174 e176
noncomputable def p177 : NestedHorner.Poly 3 := [[[-84],[0]],[[0,0],[0]],[[-1428,0],[0,0]],[[0,0],[0,0]],[[-10248,0],[0,0]],[[0,0],[0,0]],[[-40404,0],[0,0]],[[0,0],[0,0]],[[-95424,0],[0,0]],[[0,0],[0,0]],[[-138096,-84],[-84,0]],[[0,0],[0,0]],[[-120120,-672],[-672,0]],[[0,0],[0,0]],[[-58548,-1848],[-1848,0]],[[0,0],[0,0]],[[-13356,-2016],[-2016,0]],[[0,0],[0,0]],[[-756,-756],[-756,0]],[[0],[0,0]],[[0],[0,-84]]]
theorem step177 : p177=NestedArithmetic.mul p174 p176 := by decide +kernel
#print axioms step177
theorem h177 : NestedArithmetic.compile e177=p177 := StagedExprCompile.compile_times e177 e174 e176 p174 p176 p177 rfl h174 h176 step177
#print axioms h177
end Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
