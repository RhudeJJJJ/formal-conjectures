/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD36Long00CompositionalNode191
import Proofs.RadenkovicGutmanD36Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e202 : NestedArithmetic.Expr 3 := .times e191 e176
noncomputable def p202 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[70,0],[0,0]],[[0,0],[0,0]],[[856,0],[0,0]],[[0,0],[0,0]],[[5354,0],[0,0]],[[0,0],[0,0]],[[19588,0],[0,0]],[[0,0],[0,0]],[[44184,2],[2,0]],[[0,0],[0,0]],[[62044,52],[52,0]],[[0,0],[0,0]],[[52874,332],[332,0]],[[0,0],[0,0]],[[25410,840],[840,0]],[[0,0],[0,0]],[[5742,882],[882,0]],[[0,0],[0,0]],[[324,324],[324,2]],[[0],[0,0]],[[0],[0,36]]]
theorem step202 : p202=NestedArithmetic.mul p191 p176 := by decide +kernel
#print axioms step202
theorem h202 : NestedArithmetic.compile e202=p202 := StagedExprCompile.compile_times e202 e191 e176 p191 p176 p202 rfl h191 h176 step202
#print axioms h202
end Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
