/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD36Long00CompositionalNode044
import Proofs.RadenkovicGutmanD36Long00CompositionalNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e045 : NestedArithmetic.Expr 3 := .times e044 e032
noncomputable def p045 : NestedHorner.Poly 3 := [[[0],[0,36]],[[0,0],[0,0]],[[-324,324],[324,2]],[[0,0],[0]],[[90,882],[882]],[[0,0],[0]],[[6018,840],[840]],[[0,0],[0]],[[18838,332],[332]],[[0,0],[0]],[[28244,52],[52]],[[0,0],[0]],[[24408,2],[2]],[[0]],[[12756]],[[0]],[[4022]],[[0]],[[728]],[[0]],[[66]],[[0]],[[2]]]
theorem step045 : p045=NestedArithmetic.mul p044 p032 := by decide +kernel
#print axioms step045
theorem h045 : NestedArithmetic.compile e045=p045 := StagedExprCompile.compile_times e045 e044 e032 p044 p032 p045 rfl h044 h032 step045
#print axioms h045
end Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
