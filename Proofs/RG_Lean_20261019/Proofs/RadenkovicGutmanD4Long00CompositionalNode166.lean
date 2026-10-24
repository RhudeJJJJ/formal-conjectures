/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode165
import Proofs.RadenkovicGutmanD4Long00CompositionalNode121
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e166 : NestedArithmetic.Expr 3 := .times e165 e121
noncomputable def p166 : NestedHorner.Poly 3 := [[[1],[]],[[0],[0]],[[15],[0]],[[0],[0]],[[94],[0]],[[0],[0]],[[319],[0]],[[0],[0]],[[636],[0]],[[0],[0]],[[757],[1]],[[0],[0]],[[522],[7]],[[0],[0]],[[189],[16]],[[0],[0]],[[27],[13]],[[],[0]],[[],[3]]]
theorem step166 : p166=NestedArithmetic.mul p165 p121 := by decide +kernel
#print axioms step166
theorem h166 : NestedArithmetic.compile e166=p166 := StagedExprCompile.compile_times e166 e165 e121 p165 p121 p166 rfl h165 h121 step166
#print axioms h166
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
