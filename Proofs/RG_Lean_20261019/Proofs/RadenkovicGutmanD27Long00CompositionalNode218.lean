/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD27Long00CompositionalNode034
import Proofs.RadenkovicGutmanD27Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e218 : NestedArithmetic.Expr 3 := .times e034 e183
noncomputable def p218 : NestedHorner.Poly 3 := [[[-27],[0]],[[0,0],[0]],[[-432,0],[0]],[[0,0],[0]],[[-2889,0],[0]],[[0,0],[0]],[[-10476,0],[0]],[[0,0],[0]],[[-22356,0],[0]],[[0,0],[0]],[[-28512,-27],[-27]],[[0,0],[0]],[[-21033,-189],[-189]],[[0,0],[0]],[[-8100,-432],[-432]],[[0,0],[0]],[[-1215,-351],[-351]],[[0,0],[0]],[[0,-81],[-81]]]
theorem step218 : p218=NestedArithmetic.mul p034 p183 := by decide +kernel
#print axioms step218
theorem h218 : NestedArithmetic.compile e218=p218 := StagedExprCompile.compile_times e218 e034 e183 p034 p183 p218 rfl h034 h183 step218
#print axioms h218
end Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
