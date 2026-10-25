/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD45Long00CompositionalNode022
import Proofs.RadenkovicGutmanD45Long00CompositionalNode146
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e147 : NestedArithmetic.Expr 3 := .times e022 e146
noncomputable def p147 : NestedHorner.Poly 3 := [[[],[]],[[],[0]],[[],[0]],[[],[0]],[[],[0]],[[],[0]],[[],[0]],[[],[0]],[[],[0]],[[],[0]],[[],[1]]]
theorem step147 : p147=NestedArithmetic.mul p022 p146 := by decide +kernel
#print axioms step147
theorem h147 : NestedArithmetic.compile e147=p147 := StagedExprCompile.compile_times e147 e022 e146 p022 p146 p147 rfl h022 h146 step147
#print axioms h147
end Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
