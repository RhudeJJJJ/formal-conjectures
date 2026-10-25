/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD9Long00CompositionalNode174
import Proofs.RadenkovicGutmanD9Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e177 : NestedArithmetic.Expr 3 := .times e174 e176
noncomputable def p177 : NestedHorner.Poly 3 := [[[-14],[0]],[[0,0],[0]],[[-238,0],[0,0]],[[0,0],[0,0]],[[-1708,0],[0,0]],[[0,0],[0,0]],[[-6734,0],[0,0]],[[0,0],[0,0]],[[-15904,0],[0,0]],[[0,0],[0,0]],[[-23016,-14],[-14,0]],[[0,0],[0,0]],[[-20020,-112],[-112,0]],[[0,0],[0,0]],[[-9758,-308],[-308,0]],[[0,0],[0,0]],[[-2226,-336],[-336,0]],[[0,0],[0,0]],[[-126,-126],[-126,0]],[[0],[0,0]],[[0],[0,-14]]]
theorem step177 : p177=NestedArithmetic.mul p174 p176 := by decide +kernel
#print axioms step177
theorem h177 : NestedArithmetic.compile e177=p177 := StagedExprCompile.compile_times e177 e174 e176 p174 p176 p177 rfl h174 h176 step177
#print axioms h177
end Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
