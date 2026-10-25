/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD24Long00CompositionalNode034
import Proofs.RadenkovicGutmanD24Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e218 : NestedArithmetic.Expr 3 := .times e034 e183
noncomputable def p218 : NestedHorner.Poly 3 := [[[-24],[0]],[[0,0],[0]],[[-384,0],[0]],[[0,0],[0]],[[-2568,0],[0]],[[0,0],[0]],[[-9312,0],[0]],[[0,0],[0]],[[-19872,0],[0]],[[0,0],[0]],[[-25344,-24],[-24]],[[0,0],[0]],[[-18696,-168],[-168]],[[0,0],[0]],[[-7200,-384],[-384]],[[0,0],[0]],[[-1080,-312],[-312]],[[0,0],[0]],[[0,-72],[-72]]]
theorem step218 : p218=NestedArithmetic.mul p034 p183 := by decide +kernel
#print axioms step218
theorem h218 : NestedArithmetic.compile e218=p218 := StagedExprCompile.compile_times e218 e034 e183 p034 p183 p218 rfl h034 h183 step218
#print axioms h218
end Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
