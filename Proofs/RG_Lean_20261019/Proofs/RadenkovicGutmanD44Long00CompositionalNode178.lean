/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD44Long00CompositionalNode177
import Proofs.RadenkovicGutmanD44Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e178 : NestedArithmetic.Expr 3 := .times e177 e122
noncomputable def p178 : NestedHorner.Poly 3 := [[[-84],[0]],[[0,0],[0]],[[-1428,0],[0,0]],[[0,0],[0,0]],[[-10248,0],[0,0]],[[0,0],[0,0]],[[-40404,0],[0,0]],[[0,0],[0,0]],[[-95424,0],[0,0]],[[0,0],[0,0]],[[-138096,-84],[-84,0]],[[0,0],[0,0]],[[-120120,-672],[-672,0]],[[0,0],[0,0]],[[-58548,-1848],[-1848,0]],[[0,0],[0,0]],[[-13356,-2016],[-2016,0]],[[0,0],[0,0]],[[-756,-756],[-756,0]],[[0],[0,0]],[[0],[0,-84]]]
theorem step178 : p178=NestedArithmetic.mul p177 p122 := by decide +kernel
#print axioms step178
theorem h178 : NestedArithmetic.compile e178=p178 := StagedExprCompile.compile_times e178 e177 e122 p177 p122 p178 rfl h177 h122 step178
#print axioms h178
end Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
