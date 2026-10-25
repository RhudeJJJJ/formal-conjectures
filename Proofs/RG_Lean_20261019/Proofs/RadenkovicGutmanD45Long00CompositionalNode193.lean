/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD45Long00CompositionalNode192
import Proofs.RadenkovicGutmanD45Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e193 : NestedArithmetic.Expr 3 := .times e192 e122
noncomputable def p193 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[75,0],[0,0]],[[0,0],[0,0]],[[863,0],[0,0]],[[0,0],[0,0]],[[4868,0],[0,0]],[[0,0],[0,0]],[[15627,0],[0,0]],[[0,0],[0,0]],[[30132,2],[2,0]],[[0,0],[0,0]],[[35048,61],[61,0]],[[0,0],[0,0]],[[23464,404],[404,0]],[[0,0],[0,0]],[[7521,1038],[1038,0]],[[0,0],[0,0]],[[117,1098],[1098,0]],[[0,0],[0,0]],[[-405,405],[405,2]],[[0],[0,0]],[[0],[0,45]]]
theorem step193 : p193=NestedArithmetic.mul p192 p122 := by decide +kernel
#print axioms step193
theorem h193 : NestedArithmetic.compile e193=p193 := StagedExprCompile.compile_times e193 e192 e122 p192 p122 p193 rfl h192 h122 step193
#print axioms h193
end Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
