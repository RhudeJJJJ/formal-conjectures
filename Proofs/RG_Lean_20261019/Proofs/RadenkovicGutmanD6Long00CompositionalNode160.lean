/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD6Long00CompositionalNode159
import Proofs.RadenkovicGutmanD6Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e160 : NestedArithmetic.Expr 3 := .times e159 e122
noncomputable def p160 : NestedHorner.Poly 3 := [[[-4],[0]],[[0,0],[0]],[[-60,0],[0,0]],[[0,0],[0,0]],[[-376,0],[0,0]],[[0,0],[0,0]],[[-1276,0],[0,0]],[[0,0],[0,0]],[[-2544,0],[0,0]],[[0,0],[0,0]],[[-3024,-4],[-4,0]],[[0,0],[0,0]],[[-2056,-32],[-32,0]],[[0,0],[0,0]],[[-668,-88],[-88,0]],[[0,0],[0,0]],[[-12,-96],[-96,0]],[[0,0],[0,0]],[[36,-36],[-36,0]],[[0],[0,0]],[[0],[0,-4]]]
theorem step160 : p160=NestedArithmetic.mul p159 p122 := by decide +kernel
#print axioms step160
theorem h160 : NestedArithmetic.compile e160=p160 := StagedExprCompile.compile_times e160 e159 e122 p159 p122 p160 rfl h159 h122 step160
#print axioms h160
end Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
