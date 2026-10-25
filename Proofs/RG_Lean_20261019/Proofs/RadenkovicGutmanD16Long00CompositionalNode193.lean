/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD16Long00CompositionalNode192
import Proofs.RadenkovicGutmanD16Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e193 : NestedArithmetic.Expr 3 := .times e192 e122
noncomputable def p193 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[46,0],[0,0]],[[0,0],[0,0]],[[428,0],[0,0]],[[0,0],[0,0]],[[2142,0],[0,0]],[[0,0],[0,0]],[[6376,0],[0,0]],[[0,0],[0,0]],[[11688,2],[2,0]],[[0,0],[0,0]],[[13124,32],[32,0]],[[0,0],[0,0]],[[8558,172],[172,0]],[[0,0],[0,0]],[[2678,400],[400,0]],[[0,0],[0,0]],[[30,402],[402,0]],[[0,0],[0,0]],[[-144,144],[144,2]],[[0],[0,0]],[[0],[0,16]]]
theorem step193 : p193=NestedArithmetic.mul p192 p122 := by decide +kernel
#print axioms step193
theorem h193 : NestedArithmetic.compile e193=p193 := StagedExprCompile.compile_times e193 e192 e122 p192 p122 p193 rfl h192 h122 step193
#print axioms h193
end Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
