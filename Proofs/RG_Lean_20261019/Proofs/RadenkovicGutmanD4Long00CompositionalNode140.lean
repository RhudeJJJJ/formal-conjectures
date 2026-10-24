/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode122
import Proofs.RadenkovicGutmanD4Long00CompositionalNode139
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e140 : NestedArithmetic.Expr 3 := .plus e122 e139
noncomputable def p140 : NestedHorner.Poly 3 := [[[1]],[[0]],[[2]]]
theorem step140 : p140=NestedHorner.add p122 p139 := by decide +kernel
#print axioms step140
theorem h140 : NestedArithmetic.compile e140=p140 := StagedExprCompile.compile_plus e140 e122 e139 p122 p139 p140 rfl h122 h139 step140
#print axioms h140
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
