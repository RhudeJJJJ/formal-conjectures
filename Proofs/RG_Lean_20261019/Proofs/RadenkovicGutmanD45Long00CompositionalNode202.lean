/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD45Long00CompositionalNode191
import Proofs.RadenkovicGutmanD45Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e202 : NestedArithmetic.Expr 3 := .times e191 e176
noncomputable def p202 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[79,0],[0,0]],[[0,0],[0,0]],[[1009,0],[0,0]],[[0,0],[0,0]],[[6452,0],[0,0]],[[0,0],[0,0]],[[23917,0],[0,0]],[[0,0],[0,0]],[[54408,2],[2,0]],[[0,0],[0,0]],[[76840,61],[61,0]],[[0,0],[0,0]],[[65744,404],[404,0]],[[0,0],[0,0]],[[31683,1038],[1038,0]],[[0,0],[0,0]],[[7173,1098],[1098,0]],[[0,0],[0,0]],[[405,405],[405,2]],[[0],[0,0]],[[0],[0,45]]]
theorem step202 : p202=NestedArithmetic.mul p191 p176 := by decide +kernel
#print axioms step202
theorem h202 : NestedArithmetic.compile e202=p202 := StagedExprCompile.compile_times e202 e191 e176 p191 p176 p202 rfl h191 h176 step202
#print axioms h202
end Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
