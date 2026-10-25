/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD34Long00CompositionalNode159
import Proofs.RadenkovicGutmanD34Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e160 : NestedArithmetic.Expr 3 := .times e159 e122
noncomputable def p160 : NestedHorner.Poly 3 := [[[-32],[0]],[[0,0],[0]],[[-480,0],[0,0]],[[0,0],[0,0]],[[-3008,0],[0,0]],[[0,0],[0,0]],[[-10208,0],[0,0]],[[0,0],[0,0]],[[-20352,0],[0,0]],[[0,0],[0,0]],[[-24192,-32],[-32,0]],[[0,0],[0,0]],[[-16448,-256],[-256,0]],[[0,0],[0,0]],[[-5344,-704],[-704,0]],[[0,0],[0,0]],[[-96,-768],[-768,0]],[[0,0],[0,0]],[[288,-288],[-288,0]],[[0],[0,0]],[[0],[0,-32]]]
theorem step160 : p160=NestedArithmetic.mul p159 p122 := by decide +kernel
#print axioms step160
theorem h160 : NestedArithmetic.compile e160=p160 := StagedExprCompile.compile_times e160 e159 e122 p159 p122 p160 rfl h159 h122 step160
#print axioms h160
end Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
