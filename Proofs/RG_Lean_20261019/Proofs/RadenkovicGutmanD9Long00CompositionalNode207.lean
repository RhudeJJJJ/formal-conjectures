/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD9Long00CompositionalNode065
import Proofs.RadenkovicGutmanD9Long00CompositionalNode206
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e207 : NestedArithmetic.Expr 3 := .times e065 e206
noncomputable def p207 : NestedHorner.Poly 3 := [[[-2],[0]],[[0,0],[0]],[[-61,0],[0,0]],[[0,0],[0,0]],[[-685,0],[0,0]],[[0,0],[0,0]],[[-3986,0],[0,0]],[[0,0],[0,0]],[[-13585,0],[0,0]],[[0,0],[0,0]],[[-28416,-2],[-2,0]],[[0,0],[0,0]],[[-36664,-43],[-43,0]],[[0,0],[0,0]],[[-28286,-242],[-242,0]],[[0,0],[0,0]],[[-11991,-534],[-534,0]],[[0,0],[0,0]],[[-2259,-468],[-468,0]],[[0,0],[0,0]],[[-81,-135],[-135,-2]],[[0],[0,0]],[[0],[0,-9]]]
theorem step207 : p207=NestedArithmetic.mul p065 p206 := by decide +kernel
#print axioms step207
theorem h207 : NestedArithmetic.compile e207=p207 := StagedExprCompile.compile_times e207 e065 e206 p065 p206 p207 rfl h065 h206 step207
#print axioms h207
end Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
