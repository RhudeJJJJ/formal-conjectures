/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD7Long00CompositionalNode044
import Proofs.RadenkovicGutmanD7Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e062 : NestedArithmetic.Expr 3 := .times e044 e052
noncomputable def p062 : NestedHorner.Poly 3 := [[[0],[0,7]],[[0,0],[0,0]],[[63,63],[63,2]],[[0,0],[0]],[[1131,186],[186]],[[0,0],[0]],[[5197,202],[202]],[[0,0],[0]],[[11404,100],[100]],[[0,0],[0]],[[14368,23],[23]],[[0,0],[0]],[[11240,2],[2]],[[0]],[[5639]],[[0]],[[1816]],[[0]],[[363]],[[0]],[[41]],[[0]],[[2]]]
theorem step062 : p062=NestedArithmetic.mul p044 p052 := by decide +kernel
#print axioms step062
theorem h062 : NestedArithmetic.compile e062=p062 := StagedExprCompile.compile_times e062 e044 e052 p044 p052 p062 rfl h044 h052 step062
#print axioms h062
end Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
