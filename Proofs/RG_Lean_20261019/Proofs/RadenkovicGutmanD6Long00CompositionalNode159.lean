/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD6Long00CompositionalNode037
import Proofs.RadenkovicGutmanD6Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e159 : NestedArithmetic.Expr 3 := .times e037 e158
noncomputable def p159 : NestedHorner.Poly 3 := [[[-4],[0]],[[0,0],[0]],[[-60,0],[0,0]],[[0,0],[0,0]],[[-376,0],[0,0]],[[0,0],[0,0]],[[-1276,0],[0,0]],[[0,0],[0,0]],[[-2544,0],[0,0]],[[0,0],[0,0]],[[-3024,-4],[-4,0]],[[0,0],[0,0]],[[-2056,-32],[-32,0]],[[0,0],[0,0]],[[-668,-88],[-88,0]],[[0,0],[0,0]],[[-12,-96],[-96,0]],[[0,0],[0,0]],[[36,-36],[-36,0]],[[0],[0,0]],[[0],[0,-4]]]
theorem step159 : p159=NestedArithmetic.mul p037 p158 := by decide +kernel
#print axioms step159
theorem h159 : NestedArithmetic.compile e159=p159 := StagedExprCompile.compile_times e159 e037 e158 p037 p158 p159 rfl h037 h158 step159
#print axioms h159
end Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
