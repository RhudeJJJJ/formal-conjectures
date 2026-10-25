/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD36Long00CompositionalNode044
import Proofs.RadenkovicGutmanD36Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e062 : NestedArithmetic.Expr 3 := .times e044 e052
noncomputable def p062 : NestedHorner.Poly 3 := [[[0],[0,36]],[[0,0],[0,0]],[[324,324],[324,2]],[[0,0],[0]],[[5742,882],[882]],[[0,0],[0]],[[25410,840],[840]],[[0,0],[0]],[[52874,332],[332]],[[0,0],[0]],[[62044,52],[52]],[[0,0],[0]],[[44184,2],[2]],[[0]],[[19588]],[[0]],[[5354]],[[0]],[[856]],[[0]],[[70]],[[0]],[[2]]]
theorem step062 : p062=NestedArithmetic.mul p044 p052 := by decide +kernel
#print axioms step062
theorem h062 : NestedArithmetic.compile e062=p062 := StagedExprCompile.compile_times e062 e044 e052 p044 p052 p062 rfl h044 h052 step062
#print axioms h062
end Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
