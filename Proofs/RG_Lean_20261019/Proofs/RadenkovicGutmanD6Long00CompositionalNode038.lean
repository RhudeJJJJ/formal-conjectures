/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD6Long00CompositionalNode037
import Proofs.RadenkovicGutmanD6Long00CompositionalNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e038 : NestedArithmetic.Expr 3 := .times e037 e032
noncomputable def p038 : NestedHorner.Poly 3 := [[[0],[0,-4]],[[0,0],[0]],[[36,-36],[-36]],[[0,0],[0]],[[-12,-96],[-96]],[[0,0],[0]],[[-668,-88],[-88]],[[0,0],[0]],[[-2056,-32],[-32]],[[0,0],[0]],[[-3024,-4],[-4]],[[0]],[[-2544]],[[0]],[[-1276]],[[0]],[[-376]],[[0]],[[-60]],[[0]],[[-4]]]
theorem step038 : p038=NestedArithmetic.mul p037 p032 := by decide +kernel
#print axioms step038
theorem h038 : NestedArithmetic.compile e038=p038 := StagedExprCompile.compile_times e038 e037 e032 p037 p032 p038 rfl h037 h032 step038
#print axioms h038
end Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
