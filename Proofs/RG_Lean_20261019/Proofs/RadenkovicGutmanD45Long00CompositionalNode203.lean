/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD45Long00CompositionalNode202
import Proofs.RadenkovicGutmanD45Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e203 : NestedArithmetic.Expr 3 := .times e202 e122
noncomputable def p203 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[79,0],[0,0]],[[0,0],[0,0]],[[1009,0],[0,0]],[[0,0],[0,0]],[[6452,0],[0,0]],[[0,0],[0,0]],[[23917,0],[0,0]],[[0,0],[0,0]],[[54408,2],[2,0]],[[0,0],[0,0]],[[76840,61],[61,0]],[[0,0],[0,0]],[[65744,404],[404,0]],[[0,0],[0,0]],[[31683,1038],[1038,0]],[[0,0],[0,0]],[[7173,1098],[1098,0]],[[0,0],[0,0]],[[405,405],[405,2]],[[0],[0,0]],[[0],[0,45]]]
theorem step203 : p203=NestedArithmetic.mul p202 p122 := by decide +kernel
#print axioms step203
theorem h203 : NestedArithmetic.compile e203=p203 := StagedExprCompile.compile_times e203 e202 e122 p202 p122 p203 rfl h202 h122 step203
#print axioms h203
end Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
