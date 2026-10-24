/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode151
import Proofs.RadenkovicGutmanD4Long00CompositionalNode156
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e157 : NestedArithmetic.Expr 3 := .plus e151 e156
noncomputable def p157 : NestedHorner.Poly 3 := [[[1],[]],[[0,0],[0]],[[15,0],[0,0]],[[0,0],[0,0]],[[94,0],[0,0]],[[0,0],[0,0]],[[319,0],[0,0]],[[0,0],[0,0]],[[636,0],[0,0]],[[0,0],[0,0]],[[756,1],[1,0]],[[0,0],[0,0]],[[514,8],[8,0]],[[0,0],[0,0]],[[167,22],[22,0]],[[0,0],[0,0]],[[3,24],[24,0]],[[0,0],[0,0]],[[-9,9],[9,0]],[[],[0,0]],[[],[0,1]]]
theorem step157 : p157=NestedHorner.add p151 p156 := by decide +kernel
#print axioms step157
theorem h157 : NestedArithmetic.compile e157=p157 := StagedExprCompile.compile_plus e157 e151 e156 p151 p156 p157 rfl h151 h156 step157
#print axioms h157
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
