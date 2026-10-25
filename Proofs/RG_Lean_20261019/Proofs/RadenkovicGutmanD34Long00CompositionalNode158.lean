/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD34Long00CompositionalNode152
import Proofs.RadenkovicGutmanD34Long00CompositionalNode157
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e158 : NestedArithmetic.Expr 3 := .plus e152 e157
noncomputable def p158 : NestedHorner.Poly 3 := [[[1],[]],[[0,0],[0]],[[15,0],[0,0]],[[0,0],[0,0]],[[94,0],[0,0]],[[0,0],[0,0]],[[319,0],[0,0]],[[0,0],[0,0]],[[636,0],[0,0]],[[0,0],[0,0]],[[756,1],[1,0]],[[0,0],[0,0]],[[514,8],[8,0]],[[0,0],[0,0]],[[167,22],[22,0]],[[0,0],[0,0]],[[3,24],[24,0]],[[0,0],[0,0]],[[-9,9],[9,0]],[[],[0,0]],[[],[0,1]]]
theorem step158 : p158=NestedHorner.add p152 p157 := by decide +kernel
#print axioms step158
theorem h158 : NestedArithmetic.compile e158=p158 := StagedExprCompile.compile_plus e158 e152 e157 p152 p157 p158 rfl h152 h157 step158
#print axioms h158
end Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
