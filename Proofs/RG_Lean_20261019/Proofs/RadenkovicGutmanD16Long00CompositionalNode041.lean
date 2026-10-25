/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD16Long00CompositionalNode036
import Proofs.RadenkovicGutmanD16Long00CompositionalNode040
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e041 : NestedArithmetic.Expr 3 := .times e036 e040
noncomputable def p041 : NestedHorner.Poly 3 := [[[],[]],[[0],[0,-28]],[[0,0],[0]],[[324,-252],[-252]],[[0,0],[0]],[[540,-672],[-672]],[[0,0],[0]],[[-2556,-616],[-616]],[[0,0],[0]],[[-10728,-224],[-224]],[[0,0],[0]],[[-17616,-28],[-28]],[[0]],[[-15808]],[[0]],[[-8284]],[[0]],[[-2520]],[[0]],[[-412]],[[0]],[[-28]]]
theorem step041 : p041=NestedArithmetic.mul p036 p040 := by decide +kernel
#print axioms step041
theorem h041 : NestedArithmetic.compile e041=p041 := StagedExprCompile.compile_times e041 e036 e040 p036 p040 p041 rfl h036 h040 step041
#print axioms h041
end Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
