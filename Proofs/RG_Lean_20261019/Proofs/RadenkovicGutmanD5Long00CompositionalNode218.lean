/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5Long00CompositionalNode034
import Proofs.RadenkovicGutmanD5Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e218 : NestedArithmetic.Expr 3 := .times e034 e183
noncomputable def p218 : NestedHorner.Poly 3 := [[[-5],[0]],[[0,0],[0]],[[-80,0],[0]],[[0,0],[0]],[[-535,0],[0]],[[0,0],[0]],[[-1940,0],[0]],[[0,0],[0]],[[-4140,0],[0]],[[0,0],[0]],[[-5280,-5],[-5]],[[0,0],[0]],[[-3895,-35],[-35]],[[0,0],[0]],[[-1500,-80],[-80]],[[0,0],[0]],[[-225,-65],[-65]],[[0,0],[0]],[[0,-15],[-15]]]
theorem step218 : p218=NestedArithmetic.mul p034 p183 := by decide +kernel
#print axioms step218
theorem h218 : NestedArithmetic.compile e218=p218 := StagedExprCompile.compile_times e218 e034 e183 p034 p183 p218 rfl h034 h183 step218
#print axioms h218
end Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
