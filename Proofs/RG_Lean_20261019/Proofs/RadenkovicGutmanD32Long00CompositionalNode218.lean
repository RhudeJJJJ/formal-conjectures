/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD32Long00CompositionalNode034
import Proofs.RadenkovicGutmanD32Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e218 : NestedArithmetic.Expr 3 := .times e034 e183
noncomputable def p218 : NestedHorner.Poly 3 := [[[-32],[0]],[[0,0],[0]],[[-512,0],[0]],[[0,0],[0]],[[-3424,0],[0]],[[0,0],[0]],[[-12416,0],[0]],[[0,0],[0]],[[-26496,0],[0]],[[0,0],[0]],[[-33792,-32],[-32]],[[0,0],[0]],[[-24928,-224],[-224]],[[0,0],[0]],[[-9600,-512],[-512]],[[0,0],[0]],[[-1440,-416],[-416]],[[0,0],[0]],[[0,-96],[-96]]]
theorem step218 : p218=NestedArithmetic.mul p034 p183 := by decide +kernel
#print axioms step218
theorem h218 : NestedArithmetic.compile e218=p218 := StagedExprCompile.compile_times e218 e034 e183 p034 p183 p218 rfl h034 h183 step218
#print axioms h218
end Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
