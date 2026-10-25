/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD17Long00CompositionalNode177
import Proofs.RadenkovicGutmanD17Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e178 : NestedArithmetic.Expr 3 := .times e177 e122
noncomputable def p178 : NestedHorner.Poly 3 := [[[-30],[0]],[[0,0],[0]],[[-510,0],[0,0]],[[0,0],[0,0]],[[-3660,0],[0,0]],[[0,0],[0,0]],[[-14430,0],[0,0]],[[0,0],[0,0]],[[-34080,0],[0,0]],[[0,0],[0,0]],[[-49320,-30],[-30,0]],[[0,0],[0,0]],[[-42900,-240],[-240,0]],[[0,0],[0,0]],[[-20910,-660],[-660,0]],[[0,0],[0,0]],[[-4770,-720],[-720,0]],[[0,0],[0,0]],[[-270,-270],[-270,0]],[[0],[0,0]],[[0],[0,-30]]]
theorem step178 : p178=NestedArithmetic.mul p177 p122 := by decide +kernel
#print axioms step178
theorem h178 : NestedArithmetic.compile e178=p178 := StagedExprCompile.compile_times e178 e177 e122 p177 p122 p178 rfl h177 h122 step178
#print axioms h178
end Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
