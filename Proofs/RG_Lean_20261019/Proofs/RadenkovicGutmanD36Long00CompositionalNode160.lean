/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD36Long00CompositionalNode159
import Proofs.RadenkovicGutmanD36Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e160 : NestedArithmetic.Expr 3 := .times e159 e122
noncomputable def p160 : NestedHorner.Poly 3 := [[[-34],[0]],[[0,0],[0]],[[-510,0],[0,0]],[[0,0],[0,0]],[[-3196,0],[0,0]],[[0,0],[0,0]],[[-10846,0],[0,0]],[[0,0],[0,0]],[[-21624,0],[0,0]],[[0,0],[0,0]],[[-25704,-34],[-34,0]],[[0,0],[0,0]],[[-17476,-272],[-272,0]],[[0,0],[0,0]],[[-5678,-748],[-748,0]],[[0,0],[0,0]],[[-102,-816],[-816,0]],[[0,0],[0,0]],[[306,-306],[-306,0]],[[0],[0,0]],[[0],[0,-34]]]
theorem step160 : p160=NestedArithmetic.mul p159 p122 := by decide +kernel
#print axioms step160
theorem h160 : NestedArithmetic.compile e160=p160 := StagedExprCompile.compile_times e160 e159 e122 p159 p122 p160 rfl h159 h122 step160
#print axioms h160
end Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
