/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode188
import Proofs.RadenkovicGutmanD2Long00CompositionalNode156
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e189 : NestedArithmetic.Expr 3 := .times e188 e156
noncomputable def p189 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[32,0],[0,0]],[[0,0],[0,0]],[[218,0],[0,0]],[[0,0],[0,0]],[[826,0],[0,0]],[[0,0],[0,0]],[[1910,0],[0,0]],[[0,0],[0,0]],[[2784,2],[2,0]],[[0,0],[0,0]],[[2540,18],[18,0]],[[0,0],[0,0]],[[1362,60],[60,0]],[[0,0],[0,0]],[[340,92],[92,0]],[[0,0],[0,0]],[[-12,66],[66,0]],[[0,0],[0,0]],[[-18,18],[18,2]],[[0],[0,0]],[[0],[0,2]]]
theorem step189 : p189=NestedArithmetic.mul p188 p156 := by decide +kernel
#print axioms step189
theorem h189 : NestedArithmetic.compile e189=p189 := StagedExprCompile.compile_times e189 e188 e156 p188 p156 p189 rfl h188 h156 step189
#print axioms h189
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
