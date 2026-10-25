/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD18Long00CompositionalNode177
import Proofs.RadenkovicGutmanD18Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e178 : NestedArithmetic.Expr 3 := .times e177 e122
noncomputable def p178 : NestedHorner.Poly 3 := [[[-32],[0]],[[0,0],[0]],[[-544,0],[0,0]],[[0,0],[0,0]],[[-3904,0],[0,0]],[[0,0],[0,0]],[[-15392,0],[0,0]],[[0,0],[0,0]],[[-36352,0],[0,0]],[[0,0],[0,0]],[[-52608,-32],[-32,0]],[[0,0],[0,0]],[[-45760,-256],[-256,0]],[[0,0],[0,0]],[[-22304,-704],[-704,0]],[[0,0],[0,0]],[[-5088,-768],[-768,0]],[[0,0],[0,0]],[[-288,-288],[-288,0]],[[0],[0,0]],[[0],[0,-32]]]
theorem step178 : p178=NestedArithmetic.mul p177 p122 := by decide +kernel
#print axioms step178
theorem h178 : NestedArithmetic.compile e178=p178 := StagedExprCompile.compile_times e178 e177 e122 p177 p122 p178 rfl h177 h122 step178
#print axioms h178
end Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
