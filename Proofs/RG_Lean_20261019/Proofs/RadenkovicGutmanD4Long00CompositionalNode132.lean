/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode122
import Proofs.RadenkovicGutmanD4Long00CompositionalNode131
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e132 : NestedArithmetic.Expr 3 := .plus e122 e131
noncomputable def p132 : NestedHorner.Poly 3 := [[[1]],[[0]],[[4]]]
theorem step132 : p132=NestedHorner.add p122 p131 := by decide +kernel
#print axioms step132
theorem h132 : NestedArithmetic.compile e132=p132 := StagedExprCompile.compile_plus e132 e122 e131 p122 p131 p132 rfl h122 h131 step132
#print axioms h132
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
