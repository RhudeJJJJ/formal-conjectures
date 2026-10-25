/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD23Long00CompositionalNode152
import Proofs.RadenkovicGutmanD23Long00CompositionalNode175
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e176 : NestedArithmetic.Expr 3 := .plus e152 e175
noncomputable def p176 : NestedHorner.Poly 3 := [[[1],[]],[[0,0],[0]],[[17,0],[0,0]],[[0,0],[0,0]],[[122,0],[0,0]],[[0,0],[0,0]],[[481,0],[0,0]],[[0,0],[0,0]],[[1136,0],[0,0]],[[0,0],[0,0]],[[1644,1],[1,0]],[[0,0],[0,0]],[[1430,8],[8,0]],[[0,0],[0,0]],[[697,22],[22,0]],[[0,0],[0,0]],[[159,24],[24,0]],[[0,0],[0,0]],[[9,9],[9,0]],[[],[0,0]],[[],[0,1]]]
theorem step176 : p176=NestedHorner.add p152 p175 := by decide +kernel
#print axioms step176
theorem h176 : NestedArithmetic.compile e176=p176 := StagedExprCompile.compile_plus e176 e152 e175 p152 p175 p176 rfl h152 h175 step176
#print axioms h176
end Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
