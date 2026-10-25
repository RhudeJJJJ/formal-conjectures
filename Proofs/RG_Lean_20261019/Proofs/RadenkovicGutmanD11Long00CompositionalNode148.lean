/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD11Long00CompositionalNode145
import Proofs.RadenkovicGutmanD11Long00CompositionalNode147
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e148 : NestedArithmetic.Expr 3 := .plus e145 e147
noncomputable def p148 : NestedHorner.Poly 3 := [[[1],[]],[[0],[0]],[[8],[0]],[[0],[0]],[[22],[0]],[[0],[0]],[[24],[0]],[[0],[0]],[[9],[0]],[[],[0]],[[],[1]]]
theorem step148 : p148=NestedHorner.add p145 p147 := by decide +kernel
#print axioms step148
theorem h148 : NestedArithmetic.compile e148=p148 := StagedExprCompile.compile_plus e148 e145 e147 p145 p147 p148 rfl h145 h147 step148
#print axioms h148
end Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
