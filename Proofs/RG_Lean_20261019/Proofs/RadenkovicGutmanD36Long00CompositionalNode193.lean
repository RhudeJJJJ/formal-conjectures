/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD36Long00CompositionalNode192
import Proofs.RadenkovicGutmanD36Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e193 : NestedArithmetic.Expr 3 := .times e192 e122
noncomputable def p193 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[66,0],[0,0]],[[0,0],[0,0]],[[728,0],[0,0]],[[0,0],[0,0]],[[4022,0],[0,0]],[[0,0],[0,0]],[[12756,0],[0,0]],[[0,0],[0,0]],[[24408,2],[2,0]],[[0,0],[0,0]],[[28244,52],[52,0]],[[0,0],[0,0]],[[18838,332],[332,0]],[[0,0],[0,0]],[[6018,840],[840,0]],[[0,0],[0,0]],[[90,882],[882,0]],[[0,0],[0,0]],[[-324,324],[324,2]],[[0],[0,0]],[[0],[0,36]]]
theorem step193 : p193=NestedArithmetic.mul p192 p122 := by decide +kernel
#print axioms step193
theorem h193 : NestedArithmetic.compile e193=p193 := StagedExprCompile.compile_times e193 e192 e122 p192 p122 p193 rfl h192 h122 step193
#print axioms h193
end Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
