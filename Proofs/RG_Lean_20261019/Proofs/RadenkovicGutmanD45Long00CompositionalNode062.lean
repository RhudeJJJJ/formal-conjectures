/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD45Long00CompositionalNode044
import Proofs.RadenkovicGutmanD45Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e062 : NestedArithmetic.Expr 3 := .times e044 e052
noncomputable def p062 : NestedHorner.Poly 3 := [[[0],[0,45]],[[0,0],[0,0]],[[405,405],[405,2]],[[0,0],[0]],[[7173,1098],[1098]],[[0,0],[0]],[[31683,1038],[1038]],[[0,0],[0]],[[65744,404],[404]],[[0,0],[0]],[[76840,61],[61]],[[0,0],[0]],[[54408,2],[2]],[[0]],[[23917]],[[0]],[[6452]],[[0]],[[1009]],[[0]],[[79]],[[0]],[[2]]]
theorem step062 : p062=NestedArithmetic.mul p044 p052 := by decide +kernel
#print axioms step062
theorem h062 : NestedArithmetic.compile e062=p062 := StagedExprCompile.compile_times e062 e044 e052 p044 p052 p062 rfl h044 h052 step062
#print axioms h062
end Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
