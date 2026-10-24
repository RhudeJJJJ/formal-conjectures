/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode158
import Proofs.RadenkovicGutmanD2Long00CompositionalNode160
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e161 : NestedArithmetic.Expr 3 := .plus e158 e160
noncomputable def p161 : NestedHorner.Poly 3 := [[[0],[0]],[[0,0],[0]],[[4,0],[0,0]],[[0,0],[0,0]],[[56,0],[0,0]],[[0,0],[0,0]],[[324,0],[0,0]],[[0,0],[0,0]],[[1000,0],[0,0]],[[0,0],[0,0]],[[1776,0],[0,0]],[[0,0],[0,0]],[[1832,0],[0,0]],[[0,0],[0,0]],[[1060,0],[0,0]],[[0,0],[0,0]],[[312,0],[0,0]],[[0,0],[0,0]],[[36,0],[0,0]],[[0],[0,0]],[[0],[0,0]]]
theorem step161 : p161=NestedHorner.add p158 p160 := by decide +kernel
#print axioms step161
theorem h161 : NestedArithmetic.compile e161=p161 := StagedExprCompile.compile_plus e161 e158 e160 p158 p160 p161 rfl h158 h160 step161
#print axioms h161
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
