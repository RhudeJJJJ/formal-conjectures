/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode122
import Proofs.RadenkovicGutmanD4Long00CompositionalNode124
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e125 : NestedArithmetic.Expr 3 := .plus e122 e124
noncomputable def p125 : NestedHorner.Poly 3 := [[[1]],[[0]],[[3]]]
theorem step125 : p125=NestedHorner.add p122 p124 := by decide +kernel
#print axioms step125
theorem h125 : NestedArithmetic.compile e125=p125 := StagedExprCompile.compile_plus e125 e122 e124 p122 p124 p125 rfl h122 h124 step125
#print axioms h125
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
