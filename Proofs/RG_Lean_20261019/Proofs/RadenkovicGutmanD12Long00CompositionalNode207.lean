/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD12Long00CompositionalNode065
import Proofs.RadenkovicGutmanD12Long00CompositionalNode206
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e207 : NestedArithmetic.Expr 3 := .times e065 e206
noncomputable def p207 : NestedHorner.Poly 3 := [[[-2],[0]],[[0,0],[0]],[[-70,0],[0,0]],[[0,0],[0,0]],[[-832,0],[0,0]],[[0,0],[0,0]],[[-4994,0],[0,0]],[[0,0],[0,0]],[[-17356,0],[0,0]],[[0,0],[0,0]],[[-36792,-2],[-2,0]],[[0,0],[0,0]],[[-47932,-52],[-52,0]],[[0,0],[0,0]],[[-37250,-308],[-308,0]],[[0,0],[0,0]],[[-15882,-696],[-696,0]],[[0,0],[0,0]],[[-3006,-618],[-618,0]],[[0,0],[0,0]],[[-108,-180],[-180,-2]],[[0],[0,0]],[[0],[0,-12]]]
theorem step207 : p207=NestedArithmetic.mul p065 p206 := by decide +kernel
#print axioms step207
theorem h207 : NestedArithmetic.compile e207=p207 := StagedExprCompile.compile_times e207 e065 e206 p065 p206 p207 rfl h065 h206 step207
#print axioms h207
end Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
