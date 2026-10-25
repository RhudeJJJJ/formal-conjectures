/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD31Long00CompositionalNode123
import Proofs.RadenkovicGutmanD31Long00CompositionalNode140
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e141 : NestedArithmetic.Expr 3 := .plus e123 e140
noncomputable def p141 : NestedHorner.Poly 3 := [[[1]],[[0]],[[2]]]
theorem step141 : p141=NestedHorner.add p123 p140 := by decide +kernel
#print axioms step141
theorem h141 : NestedArithmetic.compile e141=p141 := StagedExprCompile.compile_plus e141 e123 e140 p123 p140 p141 rfl h123 h140 step141
#print axioms h141
end Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
