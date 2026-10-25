/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD18Long00CompositionalNode174
import Proofs.RadenkovicGutmanD18Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e177 : NestedArithmetic.Expr 3 := .times e174 e176
noncomputable def p177 : NestedHorner.Poly 3 := [[[-32],[0]],[[0,0],[0]],[[-544,0],[0,0]],[[0,0],[0,0]],[[-3904,0],[0,0]],[[0,0],[0,0]],[[-15392,0],[0,0]],[[0,0],[0,0]],[[-36352,0],[0,0]],[[0,0],[0,0]],[[-52608,-32],[-32,0]],[[0,0],[0,0]],[[-45760,-256],[-256,0]],[[0,0],[0,0]],[[-22304,-704],[-704,0]],[[0,0],[0,0]],[[-5088,-768],[-768,0]],[[0,0],[0,0]],[[-288,-288],[-288,0]],[[0],[0,0]],[[0],[0,-32]]]
theorem step177 : p177=NestedArithmetic.mul p174 p176 := by decide +kernel
#print axioms step177
theorem h177 : NestedArithmetic.compile e177=p177 := StagedExprCompile.compile_times e177 e174 e176 p174 p176 p177 rfl h174 h176 step177
#print axioms h177
end Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
