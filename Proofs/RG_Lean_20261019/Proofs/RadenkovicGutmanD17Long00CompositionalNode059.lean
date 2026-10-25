/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD17Long00CompositionalNode058
import Proofs.RadenkovicGutmanD17Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e059 : NestedArithmetic.Expr 3 := .times e058 e052
noncomputable def p059 : NestedHorner.Poly 3 := [[[],[]],[[0],[0,-30]],[[0,0],[0]],[[-270,-270],[-270]],[[0,0],[0]],[[-4770,-720],[-720]],[[0,0],[0]],[[-20910,-660],[-660]],[[0,0],[0]],[[-42900,-240],[-240]],[[0,0],[0]],[[-49320,-30],[-30]],[[0]],[[-34080]],[[0]],[[-14430]],[[0]],[[-3660]],[[0]],[[-510]],[[0]],[[-30]]]
theorem step059 : p059=NestedArithmetic.mul p058 p052 := by decide +kernel
#print axioms step059
theorem h059 : NestedArithmetic.compile e059=p059 := StagedExprCompile.compile_times e059 e058 e052 p058 p052 p059 rfl h058 h052 step059
#print axioms h059
end Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
