/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode189
import Proofs.RadenkovicGutmanD2Long00CompositionalNode120
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e190 : NestedArithmetic.Expr 3 := .times e189 e120
noncomputable def p190 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[32,0],[0,0]],[[0,0],[0,0]],[[218,0],[0,0]],[[0,0],[0,0]],[[826,0],[0,0]],[[0,0],[0,0]],[[1910,0],[0,0]],[[0,0],[0,0]],[[2784,2],[2,0]],[[0,0],[0,0]],[[2540,18],[18,0]],[[0,0],[0,0]],[[1362,60],[60,0]],[[0,0],[0,0]],[[340,92],[92,0]],[[0,0],[0,0]],[[-12,66],[66,0]],[[0,0],[0,0]],[[-18,18],[18,2]],[[0],[0,0]],[[0],[0,2]]]
theorem step190 : p190=NestedArithmetic.mul p189 p120 := by decide +kernel
#print axioms step190
theorem h190 : NestedArithmetic.compile e190=p190 := StagedExprCompile.compile_times e190 e189 e120 p189 p120 p190 rfl h189 h120 step190
#print axioms h190
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
