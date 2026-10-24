/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode144
import Proofs.RadenkovicGutmanD4Long00CompositionalNode146
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e147 : NestedArithmetic.Expr 3 := .plus e144 e146
noncomputable def p147 : NestedHorner.Poly 3 := [[[1],[]],[[0],[0]],[[8],[0]],[[0],[0]],[[22],[0]],[[0],[0]],[[24],[0]],[[0],[0]],[[9],[0]],[[],[0]],[[],[1]]]
theorem step147 : p147=NestedHorner.add p144 p146 := by decide +kernel
#print axioms step147
theorem h147 : NestedArithmetic.compile e147=p147 := StagedExprCompile.compile_plus e147 e144 e146 p144 p146 p147 rfl h144 h146 step147
#print axioms h147
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
