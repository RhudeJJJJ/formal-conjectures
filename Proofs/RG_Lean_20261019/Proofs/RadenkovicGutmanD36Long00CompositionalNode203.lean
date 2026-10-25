/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD36Long00CompositionalNode202
import Proofs.RadenkovicGutmanD36Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e203 : NestedArithmetic.Expr 3 := .times e202 e122
noncomputable def p203 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[70,0],[0,0]],[[0,0],[0,0]],[[856,0],[0,0]],[[0,0],[0,0]],[[5354,0],[0,0]],[[0,0],[0,0]],[[19588,0],[0,0]],[[0,0],[0,0]],[[44184,2],[2,0]],[[0,0],[0,0]],[[62044,52],[52,0]],[[0,0],[0,0]],[[52874,332],[332,0]],[[0,0],[0,0]],[[25410,840],[840,0]],[[0,0],[0,0]],[[5742,882],[882,0]],[[0,0],[0,0]],[[324,324],[324,2]],[[0],[0,0]],[[0],[0,36]]]
theorem step203 : p203=NestedArithmetic.mul p202 p122 := by decide +kernel
#print axioms step203
theorem h203 : NestedArithmetic.compile e203=p203 := StagedExprCompile.compile_times e203 e202 e122 p202 p122 p203 rfl h202 h122 step203
#print axioms h203
end Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
