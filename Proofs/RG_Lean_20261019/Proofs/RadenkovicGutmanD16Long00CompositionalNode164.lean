/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD16Long00CompositionalNode119
import Proofs.RadenkovicGutmanD16Long00CompositionalNode163
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e164 : NestedArithmetic.Expr 3 := .times e119 e163
noncomputable def p164 : NestedHorner.Poly 3 := [[[-28],[0]],[[0,0],[0]],[[-412,0],[0,0]],[[0,0],[0,0]],[[-2520,0],[0,0]],[[0,0],[0,0]],[[-8284,0],[0,0]],[[0,0],[0,0]],[[-15808,0],[0,0]],[[0,0],[0,0]],[[-17616,-28],[-28,0]],[[0,0],[0,0]],[[-10728,-224],[-224,0]],[[0,0],[0,0]],[[-2556,-616],[-616,0]],[[0,0],[0,0]],[[540,-672],[-672,0]],[[0,0],[0,0]],[[324,-252],[-252,0]],[[0],[0,0]],[[0],[0,-28]]]
theorem step164 : p164=NestedArithmetic.mul p119 p163 := by decide +kernel
#print axioms step164
theorem h164 : NestedArithmetic.compile e164=p164 := StagedExprCompile.compile_times e164 e119 e163 p119 p163 p164 rfl h119 h163 step164
#print axioms h164
end Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
