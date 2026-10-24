/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode150
import Proofs.RadenkovicGutmanD2Long00CompositionalNode155
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e156 : NestedArithmetic.Expr 3 := .plus e150 e155
noncomputable def p156 : NestedHorner.Poly 3 := [[[1],[]],[[0,0],[0]],[[15,0],[0,0]],[[0,0],[0,0]],[[94,0],[0,0]],[[0,0],[0,0]],[[319,0],[0,0]],[[0,0],[0,0]],[[636,0],[0,0]],[[0,0],[0,0]],[[756,1],[1,0]],[[0,0],[0,0]],[[514,8],[8,0]],[[0,0],[0,0]],[[167,22],[22,0]],[[0,0],[0,0]],[[3,24],[24,0]],[[0,0],[0,0]],[[-9,9],[9,0]],[[],[0,0]],[[],[0,1]]]
theorem step156 : p156=NestedHorner.add p150 p155 := by decide +kernel
#print axioms step156
theorem h156 : NestedArithmetic.compile e156=p156 := StagedExprCompile.compile_plus e156 e150 e155 p150 p155 p156 rfl h150 h155 step156
#print axioms h156
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
