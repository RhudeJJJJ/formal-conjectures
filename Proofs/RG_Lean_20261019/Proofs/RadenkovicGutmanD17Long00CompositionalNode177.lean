/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD17Long00CompositionalNode174
import Proofs.RadenkovicGutmanD17Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e177 : NestedArithmetic.Expr 3 := .times e174 e176
noncomputable def p177 : NestedHorner.Poly 3 := [[[-30],[0]],[[0,0],[0]],[[-510,0],[0,0]],[[0,0],[0,0]],[[-3660,0],[0,0]],[[0,0],[0,0]],[[-14430,0],[0,0]],[[0,0],[0,0]],[[-34080,0],[0,0]],[[0,0],[0,0]],[[-49320,-30],[-30,0]],[[0,0],[0,0]],[[-42900,-240],[-240,0]],[[0,0],[0,0]],[[-20910,-660],[-660,0]],[[0,0],[0,0]],[[-4770,-720],[-720,0]],[[0,0],[0,0]],[[-270,-270],[-270,0]],[[0],[0,0]],[[0],[0,-30]]]
theorem step177 : p177=NestedArithmetic.mul p174 p176 := by decide +kernel
#print axioms step177
theorem h177 : NestedArithmetic.compile e177=p177 := StagedExprCompile.compile_times e177 e174 e176 p174 p176 p177 rfl h174 h176 step177
#print axioms h177
end Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
