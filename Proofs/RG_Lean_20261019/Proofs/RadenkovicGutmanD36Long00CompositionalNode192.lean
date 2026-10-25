/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD36Long00CompositionalNode191
import Proofs.RadenkovicGutmanD36Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e192 : NestedArithmetic.Expr 3 := .times e191 e158
noncomputable def p192 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[66,0],[0,0]],[[0,0],[0,0]],[[728,0],[0,0]],[[0,0],[0,0]],[[4022,0],[0,0]],[[0,0],[0,0]],[[12756,0],[0,0]],[[0,0],[0,0]],[[24408,2],[2,0]],[[0,0],[0,0]],[[28244,52],[52,0]],[[0,0],[0,0]],[[18838,332],[332,0]],[[0,0],[0,0]],[[6018,840],[840,0]],[[0,0],[0,0]],[[90,882],[882,0]],[[0,0],[0,0]],[[-324,324],[324,2]],[[0],[0,0]],[[0],[0,36]]]
theorem step192 : p192=NestedArithmetic.mul p191 p158 := by decide +kernel
#print axioms step192
theorem h192 : NestedArithmetic.compile e192=p192 := StagedExprCompile.compile_times e192 e191 e158 p191 p158 p192 rfl h191 h158 step192
#print axioms h192
end Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
