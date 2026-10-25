/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD34Long00CompositionalNode037
import Proofs.RadenkovicGutmanD34Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e159 : NestedArithmetic.Expr 3 := .times e037 e158
noncomputable def p159 : NestedHorner.Poly 3 := [[[-32],[0]],[[0,0],[0]],[[-480,0],[0,0]],[[0,0],[0,0]],[[-3008,0],[0,0]],[[0,0],[0,0]],[[-10208,0],[0,0]],[[0,0],[0,0]],[[-20352,0],[0,0]],[[0,0],[0,0]],[[-24192,-32],[-32,0]],[[0,0],[0,0]],[[-16448,-256],[-256,0]],[[0,0],[0,0]],[[-5344,-704],[-704,0]],[[0,0],[0,0]],[[-96,-768],[-768,0]],[[0,0],[0,0]],[[288,-288],[-288,0]],[[0],[0,0]],[[0],[0,-32]]]
theorem step159 : p159=NestedArithmetic.mul p037 p158 := by decide +kernel
#print axioms step159
theorem h159 : NestedArithmetic.compile e159=p159 := StagedExprCompile.compile_times e159 e037 e158 p037 p158 p159 rfl h037 h158 step159
#print axioms h159
end Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
