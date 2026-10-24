/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode147
import Proofs.RadenkovicGutmanD4Long00CompositionalNode153
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e165 : NestedArithmetic.Expr 3 := .times e147 e153
noncomputable def p165 : NestedHorner.Poly 3 := [[[1],[]],[[0],[0]],[[15],[0]],[[0],[0]],[[94],[0]],[[0],[0]],[[319],[0]],[[0],[0]],[[636],[0]],[[0],[0]],[[757],[1]],[[0],[0]],[[522],[7]],[[0],[0]],[[189],[16]],[[0],[0]],[[27],[13]],[[],[0]],[[],[3]]]
theorem step165 : p165=NestedArithmetic.mul p147 p153 := by decide +kernel
#print axioms step165
theorem h165 : NestedArithmetic.compile e165=p165 := StagedExprCompile.compile_times e165 e147 e153 p147 p153 p165 rfl h147 h153 step165
#print axioms h165
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
